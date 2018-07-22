from subprocess import run, PIPE
from sexpdata import loads
from sklearn import tree
from sklearn import svm
import re
import graphviz
import decimal


def simple_loop(*, x, y):
    return {
        'x': x + y,
        'y': y + 1,
    }


relations = {
    'simple': {
        'head': {
            'start': {
                'x': 1,
                'y': 0,
            },
            'logic': '(and (= x 1) (= y 0))',
        },
        'loop': {
            'script': simple_loop,
            'logic': """
                (declare-const x Int)
                (declare-const y Int)
                (declare-const xp Int)
                (declare-const yp Int)

                (assert {prerel})
                (assert (= xp (+ x y)))
                (assert (= yp (+ y 1)))
                (assert (not {postrel}))

                (check-sat)
                (get-model)
            """,
        },
    },
}


def positive_points(relation):
    current = relation['head']['start']
    while True:
        yield current
        current = relation['loop']['script'](**current)


def negative_point(relation, hypothesis):
    logic = relation['loop']['logic'].format(**hypothesis)
    status = run(['z3', '-in'], input=logic, encoding='utf8', check=True, stdout=PIPE)
    status = status.stdout.splitlines()
    if status[0] != 'sat':
        print(status[0], hypothesis)
        return

    point = { key: None for key in relation['head']['start'].keys() }
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


def unscience(num):
    return str(decimal.getcontext().create_decimal(decimal.Decimal(num)))


# def tree_classify(Classifier, X, y):
#     def tree_to_z3(tree, symbols):
#         if len(tree.keys()) == 0:
#             return 'true';
#
#         children = list(map(lambda t: tree_to_z3(t, symbols), tree['sub'].values()))
#         root = linsvm_to_z3(tree['clf'], symbols)
#
#         if len(children) == 0:
#             return root
#         return '(and %s (or %s))' % (root, ' '.join(children))
#     def step(Xi, Yi):
#         clf = Classifier()
#         clf = clf.fit(Xi, Yi)

#         visualize_svm_2d(clf, Xi, Yi, 'first 10')
#         print(Xi)
#         print(Yi)
#         input()

#         wrong = [
#             pred
#             for truth, pred in zip(Yi, clf.predict(Xi))
#             if truth != pred
#         ]
#         subtree = {}
#         for clazz in wrong:
#             Xj, Yj = [], []
#             for x, truth, pred in zip(Xi, Yi, clf.predict(Xi)):
#                 if pred == clazz:
#                     Xj += [ x ]
#                     Yj += [ truth ]
#             subtree[clazz] = step(Xj, Yj)
#         return {
#             'clf': clf,
#             'sub': subtree,
#         }

#     return step(X, y)


def z3_int(num):
    if num >= 0:
        return unscience(abs(num))
    return '(- %s)' % unscience(num)


def visualize_svm_2d(clf, X, y, title):
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


# def linsvm_to_z3(clf, syms):
#     coeffs = clf.coef_[0]
#     threshold = -clf.intercept_[0]
#     notzero = lambda l: filter(lambda i: abs(i[1]) != 0, l)
#     linavg = list(map(simpl_mult, notzero(zip(syms, coeffs))))
#     if len(linavg) == 1:
#         return '(> %s %s)' % (linavg[0], z3_int(threshold))
#     else:
#         return '(> (+ %s) %s)' % (' '.join(linavg), z3_int(threshold))


def to_lst(obj):
    return list(map(lambda a: a[1], sorted(obj.items(), key=lambda a: a[0])))


def to_hyp(hyp, primed):
    return { 'prerel': hyp, 'postrel': primed(hyp) }


# def simpl_mult(params):
#     sym, coeff = params
#     if coeff == 1:
#         return sym
#     elif coeff == -1:
#         return '(- %s)' % sym
#     else:
#         return '(* %s %s)' % (sym, z3_int(coeff))


def loop(relation, goal):
    syms = list(sorted(relation['head']['start'].keys()))
    primer = re.compile('(%s)' % '|'.join(map(re.escape, syms)))
    primed = lambda expr: primer.sub('\\1p', expr)
    get_neg = lambda g: negative_point(relation, to_hyp(g, primed))

    # get seed positive points
    positive_gen = positive_points(relation)
    positives = [ to_lst(next(positive_gen)) ]

    # get an initial negative point (just try the goal)
    negatives = [ to_lst(get_neg(goal)) ]

    while True:
        print('hypothesis', goal)
        print('negatives', list(map(tuple, negatives)))

        # Gather data
        y = [ 1 for _ in positives ] + [ -1 for _ in negatives ]
        X = positives + negatives

        #
        # Old SVM way
        #
        # Train a tree of linear separators (to get 100% accuracy)
        # tree = tree_classify(lambda: svm.LinearSVC(C=0.1), X, y)
        # Get the line into a z3 expression
        # goal = tree_to_z3(tree, syms)
        # visualize_svm_2d(tree['clf'], X, y, goal)
        # input()

        # Give line to the oracle and to see if its correct
        counterexample = get_neg(goal)
        if not counterexample:
            break # no counterexamples, we're done!

        # check if we made progress
        counterexample = to_lst(counterexample)
        if counterexample in negatives:
            print('already seen counter-example %s no progress!' % str(counterexample))
            print('line', goal)
            return clf
        negatives += [ counterexample ]

        # add some more positive stuff
        positives += [ to_lst(next(positive_gen)) ]

# clf = loop(relations['simple'], '(>= x y)')


N = [(0, 0), (1, -1), (3, -2), (4, -2), (7, -3), (8, -3), (12, -4), (13, -4), (14, -4), (15, -4)]
P = [(1, 0), (1,  1), (2,  2), (4,  3), (7,  4), (11, 5), (16,  6), (22,  7), (29,  8), (37,  9)]
y = [ 1 for _ in range(10) ] + [ -1 for _ in range(10) ]
X = P + N

# tree = tree_classify(lambda: svm.LinearSVC(C=0.5), X, y)
tree = tree_classify(tree.DecisionTreeClassifier, X, y)
print(tree_to_z3(tree, ['x', 'y']))
visualize_svm_2d(tree['clf'], X, y, 'first 10')

# dot = tree.export_graphviz(clf, out_file=None, feature_names=['x', 'y'], class_names=['-', '+'], filled=True, rounded=True, special_characters=True)
# graph = graphviz.Source(dot)
# graph.render("iris")

import ipdb; ipdb.set_trace()
