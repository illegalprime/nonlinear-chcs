from subprocess import run, PIPE
from sexpdata import loads
from sklearn import tree
from sklearn import svm
import logging as logger
import re
import decimal
import os


Z3 = """
;; the comments here are an example of possible usage:
;; the live variables are x and y
{live-declare}

;; they are modified and stored in x' and y'
{prime-declare}

;; such that x' = x + y and y' = y + 1
{loop-body}

;; and there is a function p(x, y)
(define-fun p ({live-args}) Bool
  {invariant}
  )

;; and it's true at the start of each loop iteration
(assert (p {live-vars}))

;; and there's a goal g(x, y)
(define-fun g ({live-args}) Bool
  {goal}
  )

;; we want p(x, y) to be true before the loop starts.
;; if so, the head of the implication _must also_ be true.
;; if the body is false then the whole thing is true (contradiction found).
(assert (=> (and
             (p {start-values})
             )

            ;; we'd like to find x and y that break the goal after the loop
            ;; or break the goal if the loop were to never run
            ;; ALSO one that would break the loop invariant.
            ;; any of these will do, so we collect them in a dis-junction
            (or
             (not (p {prime-vars}))
             (not (g {start-values}))
             (not (g {prime-vars}))
             )))

(check-sat)
;; if this system is true it'll produce a model which will refute our invariant
;; we get those x and y values out to parse and try again
(get-model)
"""


class Relation:
    def setup(self):
        self.syms = list(sorted(self.start.keys()))
        self.primer = re.compile('(%s)' % '|'.join(map(re.escape, self.syms)))


    def logic(self, hypothesis):
        primesyms = list(map(self.prime, self.syms))
        starts = map(lambda s: str(self.start[s]), self.syms)
        def mk_loop(pair):
            var, expr = pair
            return '(assert (= {} {}))'.format(self.prime(var), expr)

        def mk_declare(var):
            return '(declare-const {} Int)'.format(var)

        def mk_arg(var):
            return '({} Int)'.format(var)

        return Z3.format(**{
            'live-declare': '\n'.join(map(mk_declare, self.syms)),
            'live-vars': ' '.join(self.syms),
            'live-args': ' '.join(map(mk_arg, self.syms)),
            'prime-declare': '\n'.join(map(mk_declare, primesyms)),
            'prime-vars': ' '.join(primesyms),
            'start-values': ' '.join(starts),
            'loop-body': '\n'.join(map(mk_loop, self.loop.items())),
            'invariant': hypothesis,
            'goal': self.goal,
        })

    def positive_points(self):
        current = self.start
        while True:
            yield current
            current = self.script(**current)


    def negative_point(self, expr):
        logic = self.logic(expr)
        logger.debug(logic)
        status = run(['z3', '-in'], input=logic, encoding='utf8', stdout=PIPE)
        status = status.stdout.splitlines()
        if status[0] != 'sat':
            return status[0]

        point = { key: None for key in self.start.keys() }
        model = loads(''.join(status[1:]))
        assert model[0].value() == 'model'
        for var in model[1:]:
            if var[1].value() in point:
                value = var[-1]
                # Convert value to integer if negative (- 1)
                if isinstance(value, list):
                    assert value[0].value() == '-'
                    value = -value[1]
                point[var[1].value()] = value
        return point


    def prime(self, expr):
        return self.primer.sub('\\1p', expr)


class SimpleRelation(Relation):
    def __init__(self, goal):
        self.goal = goal
        self.start = { 'x': 1, 'y': 0 }
        self.loop = {
            'x': '(+ x y)',
            'y': '(+ y 1)',
        }
        self.setup()

    def script(self, *, x, y):
        return {
            'x': x + y,
            'y': y + 1,
        }


class QuadraticRelation(Relation):
    def __init__(self, goal):
        self.goal = goal
        self.start = { 'x': 0, 'y': 0 }
        self.loop = {
            'x': '(+ x 1)',
            'y': '(* (+ x 1) (+ x 1))',
        }
        self.setup()

    def script(self, *, x, y):
        return {
            'x': x + 1,
            'y': (x + 1)**2,
        }


class ModuloRelation(Relation):
    def __init__(self, goal):
        self.goal = goal
        self.start = { 'x': 0, 'y': 0 }
        self.loop = {
            'x': '(+ x 2)',
            'y': '(+ y 1)',
        }
        self.setup()

    def script(self, *, x, y):
        return {
            'x': x + 2,
            'y': y + 1,
        }


def tree_to_z3(clf, syms):
    def unscience(num):
        return str(decimal.getcontext().create_decimal(decimal.Decimal(num)))

    def z3_int(num):
        if num >= 0:
            return unscience(abs(num))
        return '(- %s)' % unscience(abs(num))

    n_nodes = clf.tree_.node_count
    children_left = clf.tree_.children_left
    children_right = clf.tree_.children_right
    feature = clf.tree_.feature
    threshold = clf.tree_.threshold
    value = clf.tree_.value

    def step(idx):
        if children_left[idx] == children_right[idx]:
           if value[idx][0][0] == 0 and value[idx][0][1] > 0:
               return (True, [[]]) # found a path to the +
           return (False, [[]])    # found a path to the -

        lfound, lexprs = step(children_left[idx])
        rfound, rexprs = step(children_right[idx])

        decision = lambda d: '({dir} {var} {threshold})'.format(**{
            'var': syms[feature[idx]],
            'threshold': z3_int(threshold[idx]),
            'dir': '<=' if d == 'l' else '>',
        })

        if lfound and not rfound:
            return (True, [ p + [decision('l')] for p in lexprs ])

        elif rfound and not lfound:
            return (True, [ p + [decision('r')] for p in rexprs ])

        elif rfound and lfound:
            return (True,
                    [ p + [decision('l')] for p in lexprs ] +
                    [ p + [decision('r')] for p in rexprs ])

        return (False, None)

    def group(op, l):
        l = list(l)
        expr = ' '.join(l)
        return '({0} {1})'.format(op, expr) if len(l) > 1 else expr

    paths = step(0)[1]
    return group('or', map(lambda e: group('and', e), paths))


def visualize_2d(clf, X, y, title):
    import numpy as np
    import matplotlib.pyplot as plt
    import graphviz

    h = 0.02
    X = np.array(X)
    y = np.array(y)
    x_min, x_max = X[:, 0].min() - 1, X[:, 0].max() + 1
    y_min, y_max = X[:, 1].min() - 1, X[:, 1].max() + 1
    xx, yy = np.meshgrid(np.arange(x_min, x_max, h), np.arange(y_min, y_max, h))
    Z = clf.predict(np.c_[xx.ravel(), yy.ravel()])

    plt.clf()

    # Put the result into a color plot
    Z = Z.reshape(xx.shape)
    plt.contourf(xx, yy, Z, cmap=plt.cm.Paired, alpha=0.8)

    # Plot also the training points
    plt.scatter(X[:, 0], X[:, 1], c=y, cmap=plt.cm.Paired)
    plt.xlabel('x')
    plt.ylabel('y')
    plt.xlim(xx.min(), xx.max())
    plt.ylim(yy.min(), yy.max())
    plt.xticks(())
    plt.yticks(())
    plt.title(title)
    plt.savefig('graph.png', dpi=300)

    plt.show()

    dot = tree.export_graphviz(clf, out_file=None, feature_names=['x', 'y'],
                               class_names=['-', '+'], filled=True, rounded=True,
                               special_characters=True)
    graph = graphviz.Source(dot)
    graph.render("interpolant")


def loop(relation):
    def to_lst(obj):
        return list(map(lambda a: a[1],
                        sorted(obj.items(), key=lambda a: a[0])))

    # get seed positive points
    positive_gen = relation.positive_points()
    goal = relation.goal
    positives = []
    negatives = []

    while True:
        if len(negatives) > 0:
            logger.debug('hypothesis ' + goal)
            logger.debug('negatives ' + str(list(map(tuple, negatives))))

            # Gather data
            y = [ 1 for _ in positives ] + [ -1 for _ in negatives ]
            X = positives + negatives

            # Train a tree of linear separators (to get 100% accuracy)
            clf = tree.DecisionTreeClassifier()
            clf.fit(X, y)

            # Get the boxes into a z3 expressions
            goal = tree_to_z3(clf, relation.syms)

            # Make a pretty graph
            visualize_2d(clf, X, y, goal)
            if 'INTERACTIVE' in os.environ: input()

        # Give line to the oracle and to see if its correct
        counterexample = relation.negative_point(goal)

        if isinstance(counterexample, str):
            if counterexample == 'unsat':
                return (True, goal) # no counterexamples, we're done!
            else:
                raise Exception('unknown z3 exit line: ' + counterexample)

        # add counterexample to negative spots
        counterexample = to_lst(counterexample)
        if counterexample in negatives:
            raise Exception('already seen counter-example' + str(counterexample))
        negatives += [ counterexample ]

        # add some more positive stuff
        positives += [ to_lst(next(positive_gen)) ]

        # check if goal is unsound
        contradictions = [ n for n in negatives if n in positives ]
        if len(contradictions) > 0:
            return (False, contradictions) # return unsafe witness



if __name__ == '__main__':
    if 'DEBUG' in os.environ:
        logger.basicConfig(level=logger.DEBUG)

    class WeirdRelation(Relation):
        def __init__(self, goal):
            self.goal = goal
            self.start = { 'x': 0, 'y': 1 }
            self.loop = {
                'x': 'y',
                'y': '(+ x y)'
            }
            self.setup()

        def script(self, *, x, y):
            return {
                'x': y,
                'y': y + x,
            }

    # success, interpolant = loop(ModuloRelation('(= x (* y 2))'))
    # success, interpolant = loop(SimpleRelation('(>= x y)'))
    success, interpolant = loop(QuadraticRelation('(= y (* x x))'))
    # success, interpolant = loop(WeirdRelation('(>= y x)'))

    if success:
        print('success', interpolant)
    else:
        print('failure', interpolant)
