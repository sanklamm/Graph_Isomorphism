

import os
import sys
import networkx as nx
from networkx import Graph
import matplotlib.pyplot as plt
import numpy as np
import scipy as sp
from collections import OrderedDict
from itertools import permutations, chain
from itertools import islice
from sys import stdin
import time
import math
import example1 as ex1
import example2 as ex2
import example3 as ex3
import example4 as ex4
import example5 as ex5
import example6 as ex6
import example7 as ex7
import example8 as ex8

# Method to time other methods
def timeit(method):

    def timed(*args, **kw):
        ts = time.time()
        result = method(*args, **kw)
        te = time.time()
        print('%r %2.8f sec' % \
              (method.__name__, te-ts))
        return result
    return timed

class GraphIsoTester:

    def __init__(self, g1=Graph(), g2=Graph()):
        self.g1 = g1				# first networkx graph
        self.e1 = self.g1.adjacency_list()	# adjacency list of g1
        self.l1 = len(self.e1)			# amount of nodes of g1
        self.g2 = g2				# second networkx graph
        self.e2 = self.g2.adjacency_list()	# adjacency list of g2
        self.l2 = len(self.e2)			# amount of nodes of g2
        self.nc1 = [-1 for i in range(self.l1)]				# nc1[i] is the colour of the node of g1 labeled i
        self.nc2 = [-1 for i in range(self.l2)]				# nc2[i] is the colour of the node of g2 labeled i
        self.cc1 = []			# list of colour classes of g1
        self.cc2 = []			# list of colour classes of g2
        self.aoc = 0				# amount of colours
        self.deg1 = []              # degree of each node of g1
        self.deg2 = []              # degree of each node of g2
        self.keymaps = []
        self.balances = []
        #self.is_stable = False

        # Initialize node degrees
        for i in self.e1:
            self.deg1.append(len(i))

        for i in self.e2:
            self.deg2.append(len(i))

        # Initialize atom-coloring
        if (self.l1 < self.l2) :
            degs = [-1 for i in range(self.l2)]
            for i in range(self.l1) :
                color = degs[len(self.e1[i])]
                if (color == -1) :
                    degs[len(self.e1[i])] = self.aoc
                    self.cc1.append([i])
                    self.cc2.append([])
                    self.nc1[i] = self.aoc
                    self.aoc = self.aoc + 1
                else :
                    self.cc1[color].append(i)
                    self.nc1[i] = color
                color = degs[len(self.e2[i])]
                if (color == -1) :
                    degs[len(self.e2[i])] = self.aoc
                    self.cc2.append([i])
                    self.cc1.append([])
                    self.nc2[i] = self.aoc
                    self.aoc = self.aoc + 1
                else :
                    self.cc2[color].append(i)
                    self.nc2[i] = color
            for i in range(self.l1, self.l2) :
                color = degs[len(self.e2[i])]
                if (color == -1) :
                    degs[len(self.e2[i])] = self.aoc
                    self.cc2.append([i])
                    self.cc1.append([])
                    self.nc2[i] = self.aoc
                    self.aoc = self.aoc + 1
                else :
                    self.cc2[color].append(i)
                    self.nc2[i] = color
        else :
            degs = [-1 for i in range(self.l1)]
            for i in range(self.l2) :
                color = degs[len(self.e1[i])]
                if (color == -1) :
                    degs[len(self.e1[i])] = self.aoc
                    self.cc1.append([i])
                    self.cc2.append([])
                    self.nc1[i] = self.aoc
                    self.aoc = self.aoc + 1
                else :
                    self.cc1[color].append(i)
                    self.nc1[i] = color
                color = degs[len(self.e2[i])]
                if (color == -1) :
                    degs[len(self.e2[i])] = self.aoc
                    self.cc2.append([i])
                    self.cc1.append([])
                    self.nc2[i] = self.aoc
                    self.aoc = self.aoc + 1
                else :
                    self.cc2[color].append(i)
                    self.nc2[i] = color
            for i in range(self.l2, self.l1) :
                color = degs[len(self.e1[i])]
                if (color == -1) :
                    degs[len(self.e1[i])] = self.aoc
                    self.cc1.append([i])
                    self.cc2.append([])
                    self.nc1[i] = self.aoc
                    self.aoc = self.aoc + 1
                else :
                    self.cc1[color].append(i)
                    self.nc1[i] = color

###############################################################################
######################### Methods to color the nodes ##########################
###############################################################################

    # refines a balanced coloring in global data structures; nodes with the same color must not have different degrees; returns True if the previous coloring was stable (nothing has changed), False otherwise
    def fast_refined_coloring (self) :
        stable = True       # boolean wether the previous coloring was stable or not
        aoc = 0             # amount of (new) colors
        new_cc1 = []        # new colorclasses of g1 that are to create
        new_cc2 = []        # new colorclasses of g2 that are to create
        new_nc1 = list(self.nc1)    # new map node of g1 -> its color
        new_nc2 = list(self.nc2)    # new map node of g2 -> its color
        for i in range(self.aoc) :     # for each color i
            keymap = {}
            for j in range(len(self.cc1[i])) :      # for each label j in the colorclass of i
                ccomm1 = [0 for x in range(self.aoc)]      # ccomm1[x] represents the commonness of the color x in the neighbourhood of j in g1
                ccomm2 = list(ccomm1)                           # ccomm2[x] represents the commonness of the color x in the neighbourhood of j in g2
                for k in range(len(self.e1[self.cc1[i][j]])) :
                    ccomm1[self.nc1[self.e1[self.cc1[i][j]][k]]] = ccomm1[self.nc1[self.e1[self.cc1[i][j]][k]]] + 1
                    ccomm2[self.nc2[self.e2[self.cc2[i][j]][k]]] = ccomm2[self.nc2[self.e2[self.cc2[i][j]][k]]] + 1
                ckey1 = ""
                ckey2 = ""
                for k in range(self.aoc) :     # translate commoness-lists in String-format
                    ckey1 = ckey1 + str(ccomm1[k]) + "|"
                    ckey2 = ckey2 + str(ccomm2[k]) + "|"
                if (ckey1 in keymap) :     # add node of g1 labeled j to the colorclass of the color mapped in keymap
                    color = keymap[ckey1]
                    new_cc1[color].append(self.cc1[i][j])
                    new_nc1[self.cc1[i][j]] = color
                else :         # map key of neighbourhood of node of g1 labeled j on a new color and add this node to that colorclass
                    if (aoc != i) :     # color of a node has changed
                        stable = False
                    keymap[ckey1] = aoc     # aoc is the next unused color
                    new_cc1.append([self.cc1[i][j]])
                    new_cc2.append([])
                    new_nc1[self.cc1[i][j]] = aoc
                    aoc = aoc + 1
                if (ckey2 in keymap) :     # add node of g2 labeled j to the colorclass of the color mapped in keymap
                    color = keymap[ckey2]
                    new_cc2[color].append(self.cc2[i][j])
                    new_nc2[self.cc2[i][j]] = color
                else :         # map key of neighbourhood of node of g2 labeled j on a new color and add this node to that colorclass
                    if (aoc != i) :     # color of a node has changed
                        stable = False
                    keymap[ckey2] = aoc
                    new_cc2.append([self.cc2[i][j]])
                    new_cc1.append([])
                    new_nc2[self.cc2[i][j]] = aoc
                    aoc = aoc + 1
        self.cc1 = new_cc1
        self.cc2 = new_cc2
        self.nc1 = new_nc1
        self.nc2 = new_nc2
        self.aoc = aoc
        return stable


    def left_refined_coloring (self) :
        stable = True       # boolean wether the previous coloring was stable or not
        aoc = 0            # amount of (new) colors
        new_cc1 = []        # new colorclasses of g1 that are to create
        new_nc1 = list(self.nc1)    # new map node of g1 -> its color
        self.keymaps.append([])
        self.balances.append([])
        for i in range(self.aoc) :     # for each color i
            keymap = {}
            for j in range(len(self.cc1[i])) :      # for each label j in the colorclass of i
                ccomm1 = [0 for x in range(self.aoc)]      # ccomm1[x] represents the commonness of the color x in the neighbourhood of j in g1
                for k in range(len(self.e1[self.cc1[i][j]])) :
                    ccomm1[self.nc1[self.e1[self.cc1[i][j]][k]]] = ccomm1[self.nc1[self.e1[self.cc1[i][j]][k]]] + 1
                ckey1 = ""
                for k in range(self.aoc) :     # translate commoness-lists in String-format
                    ckey1 = ckey1 + str(ccomm1[k]) + "|"
                if (ckey1 in keymap) :     # add node of g1 labeled j to the colorclass of the color mapped in keymap
                    color = keymap[ckey1]
                    new_cc1[color].append(self.cc1[i][j])
                    new_nc1[self.cc1[i][j]] = color
                    self.balances[-1][color] = self.balances[-1][color] + 1
                else :         # map key of neighbourhood of node of g1 labeled j on a new color and add this node to that colorclass
                    if (aoc != i) :
                        stable = False
                    keymap[ckey1] = aoc     # aoc is the next unused color
                    new_cc1.append([self.cc1[i][j]])
                    new_nc1[self.cc1[i][j]] = aoc
                    aoc = aoc + 1
                    self.balances[-1].append(1)
            self.keymaps[-1].append(keymap)
        #stable = self.aoc == aoc
        self.cc1 = new_cc1
        self.nc1 = new_nc1
        self.aoc = aoc
        return stable

    # @timeit
    def recursive_coloring (self, old_cc, old_nc, old_aoc, loc, n, x) :

        if (n == len(loc)) :
            if len(self.cc1) != len(old_cc):
                return False
            for color in range(self.l1):
                if len(self.cc1[color]) != len(old_cc[color]):
                    return False
            return True

        if (loc[n] >= len(old_cc)) :
            return False

        for node in range(len(old_cc[loc[n]])) :
            y = x
            cc = [[x for x in l if x != old_cc[loc[n]][node]] for l in old_cc]
            nc = list(old_nc)
            nc[old_cc[loc[n]][node]] = old_aoc
            cc.append([old_cc[loc[n]][node]])
            #del(cc[loc[n]][node])
            aoc = old_aoc + 1

            br = False

            not_stable = True
            while (not_stable) :
                balances = []
                not_stable = False
                new_aoc = 0             # amount of (new) colors
                new_cc = []        # new colorclasses of g3 that are to create
                new_nc = list(nc)    # new map node of g3 -> its color
                for i in range(aoc) :     # for each color i
                    for j in range(len(cc[i])) :      # for each label j in the colorclass of i
                        ccomm = [0 for x in range(aoc)]      # ccomm1[x] represents the commonness of the color x in the neighbourhood of j in g3
                        for k in range(len(self.e2[cc[i][j]])) :
                            ccomm[nc[self.e2[cc[i][j]][k]]] = ccomm[nc[self.e2[cc[i][j]][k]]] + 1
                        ckey = ""
                        for k in range(aoc) :     # translate commoness-lists in String-format
                            ckey = ckey + str(ccomm[k]) + "|"
                        if (ckey in self.keymaps[y][i]) :     # add node of g1 labeled j to the colorclass of the color mapped in keymap
                            color = self.keymaps[y][i][ckey]
                            if (color != i) :
                                not_stable = True
                            for k in range (new_aoc, color + 1) :
                                new_cc.append([])
                                balances.append(0)
                                new_aoc = new_aoc + 1
                            new_cc[color].append(cc[i][j])
                            new_nc[cc[i][j]] = color
                            balances[color] = balances[color] + 1
                            if (balances[color] > self.balances[y][color]) :
                                br = True
                                break
                        else :
                            br = True
                            break
                    if (br) :
                        break
                if (br) :
                   break

                for color in range(new_aoc) :
                    if (balances[color] != self.balances[y][color]) :
                        br = True
                        break
                if (br) :
                    break

                y = y + 1
                cc = new_cc
                nc = new_nc
                self.cc2 = cc
                self.nc2 = nc
                aoc = new_aoc

            if (br) :
                if (node + 1 < len(old_cc[loc[n]])) :
                    continue
                else :
                    break

            if(self.recursive_coloring(cc, nc, aoc, loc, n+1, y)) :
                return True

        return False

##################################### END #####################################


###############################################################################
############################# Isomorphism Tester ##############################
###############################################################################


    # @timeit
    def has_isomorphism (self) :
        if (self.isEqual()) :
            return True
        if (self.l1 != self.l2) :
            return False
        if (len(self.g1.edges()) != len(self.g2.edges())) :
            return False
        while (True) :
                if (not self.is_balanced()) :
                    return False
                if (self.fast_refined_coloring()) :
                    break
        if (self.aoc == self.l1) :
            return True
        
        color = 0
        loc = []
        while (True) :
            if (len(self.cc1[color]) > 1) :
                break
            color = color + 1
        loc.append(color)
        self.nc1[self.cc1[color][0]] = self.aoc
        self.cc1.append([self.cc1[color][0]])
        self.aoc = self.aoc + 1
        self.cc1[color] = self.cc1[color][1:]

        self.keymap = [{} for i in range(self.aoc)]

        while (not self.left_refined_coloring()) :
            continue

        while (not self.aoc == self.l1) :
            while (True) :
                if (len(self.cc1[color]) > 1) :
                    break
                color = color + 1   
            loc.append(color)
            self.nc1[self.cc1[color][0]] = self.aoc
            self.cc1.append([self.cc1[color][0]])
            self.aoc = self.aoc + 1
            self.cc1[color] = self.cc1[color][1:]
            while (not self.left_refined_coloring()) :
                continue
    
        return self.recursive_coloring(self.cc2, self.nc2, len(self.cc2), loc, 0, 0)

    # @timeit
    def brute_iso (self) :
        print("--- BRUTE ---")
        # disregard graphs that are equal, have same amount of nodes,
        # same amount of edges and that are nor balanced
        if (self.isEqual()) :
            return True
        if (self.l1 != self.l2) :
            return False
        if (len(self.g1.edges()) != len(self.g2.edges())) :
            return False
        if (not self.is_balanced()):
            return False
        start = time.clock()
        # compute all permutations on color classes
        dictionary = list(chain.from_iterable(self.cc2))
        permut = self.partial_permutations(self.cc1)
        g1_permutations = self.translate_permutations(permut, dictionary)
        # print("dictionary: ", dictionary)
        # print("permut: ", permut)
        # print("g1_permutations: ", g1_permutations)
        # print("g1_Nodes: ", self.g1.nodes())
        # print("g2_Nodes: ", self.g2.nodes())
        #print(g1_permutations)
        #elapsed = time.clock()
        #elapsed = elapsed - start
        #num_perm = len(g1_permutations)
        #print("Time spent in (generating permutations) is: ", elapsed)
        #print("Number of permutations generated: ", num_perm)
        #progress = math.floor(num_perm/10)
        ad_mat_g2 = nx.to_numpy_matrix(self.g2)
        #i=0
        # compare each permutation of G with H

        for perms in g1_permutations:
            #i = i+1
            '''
            if i % progress == 0:
                print("10%% of brute_iso is done.")
            '''
            ad_mat_g1 = nx.to_numpy_matrix(self.g1, perms)
            # print(nx.to_numpy_matrix(self.g1))
            # print("ad_mat_g1: ")
            # print(ad_mat_g1)
            # print("ad_mat_g2: ")
            # print(ad_mat_g2)
            if (np.array_equal(ad_mat_g1, ad_mat_g2)):
                return True
        return False

##################################### END #####################################





###############################################################################
############################### Helper Methods ################################
###############################################################################
    # O(n)
    def is_balanced (self):
        # Compare the amount of color classes
        if len(self.cc1) != len(self.cc2):
            print("Both graphs have a different amount of color classes --> not balanced.")
            return False
        # In each color class compare the amount of colors
        for color in range(self.aoc):
            if len(self.cc1[color]) != len(self.cc2[color]):
                print("Both graphs have a different amount of colors in a color class --> not balanced.")
                return False
        return True


    def isEqual (self) :
        # compare amount of nodes
        if (self.l1 != self.l2) :
            return False
        # for each node compare the amount of edges
        for i in range(self.l1) :
            if (len(self.e1[i]) != len(self.e2[i])) :
                return False
            for j in range(len(self.e1[i])) :
                if (self.e1[i][j] != self.e2[i][j]) :
                    return False
        print("Both graphs are equal.")
        return True


    def partial_permutations(self, l1):
        r = [[]]
        for color in l1:
            t = []
            for perm in permutations(color):
                for par_permut in r:
                    t.append(par_permut + list(perm))
            r = t
        return r


    def translate_permutations(self, permutations, dictionary):
        result = []
        for perm in permutations:
            translator = dict(zip(tuple(dictionary), tuple(perm)))
            trans_perm = []
            for label in range(len(dictionary)):
                trans_perm.append(translator[label])
            result.append(trans_perm)
        return result

###############################################################################
############################### Output Methods ################################
###############################################################################

    def plot_graphs(self):
        # draw lables
        # choose same layout as in drawing the rest of the graph
        pos_G=nx.circular_layout(self.g1)   # positions for all nodes for G (in this case circular)
        pos_H=nx.circular_layout(self.g2)   # positions for all nodes for H (in this case circular)
        labels_G = {}                 # create a dict with labels
        for item in self.g1.nodes():
            labels_G[item] = item

        labels_H = {}                 # create a dict with labels
        for item in self.g2.nodes():
            labels_H[item] = item

        # color-mapping via numpy
        # list of cmaps can be found here: http://matplotlib.org/examples/color/colormaps_reference.html
        # I chose this cmap because there are no dark colors in it so the labels stay readable regardless
        # the color of the label.
        plt.subplots_adjust(left=0,right=1,bottom=0,top=0.95,wspace=0.01,hspace=0.01)
        plt.subplot(121)
        plt.title("Graph G")
        nx.draw_circular(self.g1, cmap=plt.get_cmap('Set1'), node_color=self.nc1)
        nx.draw_networkx_labels(self.g1, pos_G, labels_G)

        plt.subplot(122)
        plt.title("Graph H")
        nx.draw_circular(self.g2, cmap=plt.get_cmap('Set1'), node_color=self.nc2)
        nx.draw_networkx_labels(self.g2, pos_H, labels_H)

        plt.show()


    def print_isomorphism(self):
        dictionary = list(chain.from_iterable(self.cc2))
        permut = self.partial_permutations(self.cc1)
        isomorphism = self.translate_permutations(permut, dictionary)
        print("The isomorphism is: ", isomorphism[0])


    def properties(self):
        print("----------------------------------------------------------------------")
        print("------------------------------ NEW TEST ------------------------------")
        print("----------------------------------------------------------------------")
        print("Graph G has:")
        print(self.l1, " nodes")
        print(len(self.e1), " edges")
        print(sorted(self.deg1), " node-degrees")
        print("and this adjacency list:")
        print(self.e1)
        print("----------------------------------------------------------------------")
        print("Graph H has:")
        print(self.l2, " nodes")
        print(len(self.e2), " edges")
        print(sorted(self.deg2), " node-degrees")
        print("and this adjacency list:")
        print(self.e2)
        print("----------------------------------------------------------------------")

##################################### END #####################################


def read_graphs_from_files():#fp):
    dir_content = os.listdir(path='./examples')
    # dir_content = os.listdir(path=fp)
    sorted_dir_content = sorted(dir_content)
    for i in range(0,len(sorted_dir_content), 2):
        file_content_1 = open('./examples/'+dir_content[i])
        file_content_2 = open('./examples/'+dir_content[i+1])
        # file_content_1 = open(fp+dir_content[i])
        # file_content_2 = open(fp+dir_content[i+1])
        t_1 = [line.strip('e ').rstrip() for line in file_content_1]
        t_1 = t_1[1:]
        graph_1 = [tuple(map(int, t.split())) for t in t_1]
        t_2 = [line.strip('e ').rstrip() for line in file_content_2]
        t_2 = t_2[1:]
        graph_2 = [tuple(map(int, t.split())) for t in t_2]
        A = nx.Graph(graph_1)
        B = nx.Graph(graph_2)
        testing(A, B)
        # competition(A, B)

# @timeit
def competition(G, H):
    x = GraphIsoTester(G, H)
    while (x.is_balanced()) :
        if(x.fast_refined_coloring()) :
            break
    status = x.brute_iso()
    f = open('out', 'a')
    if status == True:
        f.write('1\n')
    else:
        f.write('0\n')
    f.close()

def testing(G, H):
    x = GraphIsoTester(G, H)
    x.properties()
    # Plot the initialized graphs (with atom-coloring)
    x.plot_graphs()
    # Refine Colors
    while (x.is_balanced()) :
        print("refining colors...")
        if(x.fast_refined_coloring()) :
            break
    # Plot with refined colors
    x.plot_graphs()

    # Brute force over color refined graph
    start = time.clock()
    print("Brute -- should be", nx.is_isomorphic(x.g1, x.g2), " -- : ", x.brute_iso())
    elapsed = time.clock()
    elapsed = elapsed - start
    print("Time spent in (brute_iso) is: ", elapsed)

    # Branching
    # start timing
    print("Start calc")
    start = time.clock()
    iso_test = x.has_isomorphism()
    print("HAS_ISO: " + str(iso_test))
    elapsed = time.clock()
    elapsed = elapsed - start
    print("Time spent: ", elapsed)
    # Print the isomorphism
    if iso_test:
        x.print_isomorphism()
    # Plot discrete colored graph
    x.plot_graphs()
    # Compare with built-in isomorphism tester
    print("Start built-in tester")
    start = time.clock()
    print("built in tester: ", nx.is_isomorphic(x.g1, x.g2))
    elapsed = time.clock()
    elapsed = elapsed - start
    print("Time spent: ", elapsed)
    print("----------------------------------------------------------------------")

'''
# folder_path = sys.argv[1]
# print("given path: ", folder_path)
# empty the output file
f = open('out', 'w')
f.seek(0)
f.truncate()
f.close()

read_graphs_from_files()
# read_graphs_from_files(folder_path)
'''


# To show equality
# testing(ex1.A, ex1.B)

# To show unbalanced
# testing(ex2.A, ex2.B)

# To show brute_iso
# One quick example --> 15 sec
# testing(ex3.A, ex3.B)

# One slow example --> 123 sec
testing(ex4.A, ex4.B)

# Regular graphs
# A~B = True    (1.5s)
testing(ex5.A, ex5.B)

# Regular graphs
# A~B = False   (27s)
testing(ex6.A, ex6.B)

# To show refined_coloring
# A - B: 4x
testing(ex7.A, ex7.B)

# Big-ass graph
testing(nx.random_regular_graph(20, 500, seed = 1), nx.random_regular_graph(20, 500, seed = 3))
