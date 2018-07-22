from subprocess import run, PIPE
from sexpdata import loads
from sklearn import tree
from sklearn import svm
import logging as logger
import re
import graphviz
import decimal
import os


class Relation:
    def setup(self):
        self.syms = list(sorted(self.start.keys()))
        self.primer = re.compile('(%s)' % '|'.join(map(re.escape, self.syms)))


    def logic(self, expr):
        hypothesis = self.to_hypo(expr)
        def mk_declare(sym):
            return """
            (declare-const {0} Int)
            (declare-const {0}p Int)
            """.format(sym)
        return """
        {declare}

        (assert {prerel})
        {asserts}
        (assert (not {postrel}))

        (check-sat)
        (get-model)
        """.format(**{
            'declare': '\n'.join(map(mk_declare, self.syms)),
            'asserts': '\n'.join(map(lambda a: '(assert %s)' % a, self.asserts)),
            'prerel': hypothesis['prerel'],
            'postrel': hypothesis['postrel'],
        })

    def positive_points(self):
        current = self.start
        while True:
            yield current
            current = self.script(**current)


    def negative_point(self, expr):
        logic = self.logic(expr)
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


    def to_hypo(self, expr):
        return {
            'prerel': expr,
            'postrel': self.primer.sub('\\1p', expr),
        }


class SimpleRelation(Relation):
    def __init__(self):
        self.start = { 'x': 1, 'y': 0 }
        self.start_logic = '(and (= x 1) (= y 0))' # TODO: when do we need this?
        self.asserts = [
            '(= xp (+ x y))',
            '(= yp (+ y 1))',
        ]
        self.setup()

    def script(self, *, x, y):
        return {
            'x': x + y,
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

        lfound, lepxrs = step(children_left[idx])
        rfound, rexprs = step(children_right[idx])

        decision = lambda d: '({dir} {var} {threshold})'.format(**{
            'var': syms[feature[idx]],
            'threshold': z3_int(threshold[idx]),
            'dir': '<=' if d == 'l' else '>',
        })

        if lfound and not rfound:
            return (True, [ p + [decision('l')] for p in lepxrs ])

        elif rfound and not lfound:
            return (True, [ p + [decision('r')] for p in rexprs ])

        elif rfound and lfound:
            return (True, lexprs + rexprs)

        return (False, None)

    paths = step(0)[1]
    conj = list(map(lambda e: '(and {})'.format(' '.join(e)), paths))
    disj = '(or {})'.format(' '.join(conj)) if len(conj) > 1 else conj[0]

    return disj


def visualize_2d(clf, X, y, title):
    import numpy as np
    import matplotlib.pyplot as plt

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


def loop(relation, goal):
    def to_lst(obj):
        return list(map(lambda a: a[1],
                        sorted(obj.items(), key=lambda a: a[0])))

    # get seed positive points
    positive_gen = relation.positive_points()
    positives = [ to_lst(next(positive_gen)) ]

    # get an initial negative point (just try the goal)
    negatives = [ to_lst(relation.negative_point(goal)) ]

    while True:
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
        if 'INTERACTIVE' in os.environ:
            visualize_2d(clf, X, y, goal)
            input()

        # Give line to the oracle and to see if its correct
        counterexample = relation.negative_point(goal)

        if isinstance(counterexample, str):
            if counterexample == 'unsat':
                return goal # no counterexamples, we're done!
            else:
                raise 'unknown z3 exit line: ' + counterexample

        # add counterexample to negative spots
        counterexample = to_lst(counterexample)
        if counterexample in negatives:
            raise 'already seen counter-example %s no progress!' % str(counterexample)
        negatives += [ counterexample ]

        # add some more positive stuff
        positives += [ to_lst(next(positive_gen)) ]


if 'DEBUG' in os.environ:
    logger.basicConfig(level=logger.DEBUG)

interpolant = loop(SimpleRelation(), '(>= x y)')
print('success', interpolant)


# N = [(0, 0), (1, -1), (3, -2), (4, -2), (7, -3), (8, -3), (12, -4), (13, -4), (14, -4), (15, -4)]
# P = [(1, 0), (1,  1), (2,  2), (4,  3), (7,  4), (11, 5), (16,  6), (22,  7), (29,  8), (37,  9)]
# y = [ 1 for _ in range(10) ] + [ -1 for _ in range(10) ]
# X = P + N
# clf = tree.DecisionTreeClassifier()
# clf.fit(X, y)
# visualize_2d(clf, X, y, 'first 10')
# logger.debug(tree_to_z3(clf, ['x', 'y']))
# dot = tree.export_graphviz(clf, out_file=None, feature_names=['x', 'y'], class_names=['-', '+'], filled=True, rounded=True, special_characters=True)
# graph = graphviz.Source(dot)
# graph.render("iris")
