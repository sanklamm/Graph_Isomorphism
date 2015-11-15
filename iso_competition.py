

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

class GraphIsoTester:

    def __init__(self, g1=Graph(), g2=Graph()):
        self.g1 = g1
        self.e1 = self.g1.adjacency_list()
        self.l1 = len(self.e1)
        self.g2 = g2
        self.e2 = self.g2.adjacency_list()
        self.l2 = len(self.e2)
        self.nc1 = [-1 for i in range(self.l1)]
        self.nc2 = [-1 for i in range(self.l2)]
        self.cc1 = []
        self.cc2 = []
        self.aoc = 0
        self.deg1 = []
        self.deg2 = []
        self.keymaps = []
        self.balances = []

        for i in self.e1:
            self.deg1.append(len(i))

        for i in self.e2:
            self.deg2.append(len(i))

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

    def fast_refined_coloring (self) :
        stable = True
        aoc = 0
        new_cc1 = []
        new_cc2 = []
        new_nc1 = list(self.nc1)
        new_nc2 = list(self.nc2)
        for i in range(self.aoc) :
            keymap = {}
            for j in range(len(self.cc1[i])) :
                ccomm1 = [0 for x in range(self.aoc)]
                ccomm2 = list(ccomm1)
                for k in range(len(self.e1[self.cc1[i][j]])) :
                    ccomm1[self.nc1[self.e1[self.cc1[i][j]][k]]] = ccomm1[self.nc1[self.e1[self.cc1[i][j]][k]]] + 1
                    ccomm2[self.nc2[self.e2[self.cc2[i][j]][k]]] = ccomm2[self.nc2[self.e2[self.cc2[i][j]][k]]] + 1
                ckey1 = ""
                ckey2 = ""
                for k in range(self.aoc) :
                    ckey1 = ckey1 + str(ccomm1[k]) + "|"
                    ckey2 = ckey2 + str(ccomm2[k]) + "|"
                if (ckey1 in keymap) :
                    color = keymap[ckey1]
                    new_cc1[color].append(self.cc1[i][j])
                    new_nc1[self.cc1[i][j]] = color
                else :
                    if (aoc != i) :
                        stable = False
                    keymap[ckey1] = aoc
                    new_cc1.append([self.cc1[i][j]])
                    new_cc2.append([])
                    new_nc1[self.cc1[i][j]] = aoc
                    aoc = aoc + 1
                if (ckey2 in keymap) :
                    color = keymap[ckey2]
                    new_cc2[color].append(self.cc2[i][j])
                    new_nc2[self.cc2[i][j]] = color
                else :
                    if (aoc != i) :
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
        stable = True
        aoc = 0
        new_cc1 = []
        new_nc1 = list(self.nc1)
        self.keymaps.append([])
        self.balances.append([])
        for i in range(self.aoc) :
            keymap = {}
            for j in range(len(self.cc1[i])) :
                ccomm1 = [0 for x in range(self.aoc)]
                for k in range(len(self.e1[self.cc1[i][j]])) :
                    ccomm1[self.nc1[self.e1[self.cc1[i][j]][k]]] = ccomm1[self.nc1[self.e1[self.cc1[i][j]][k]]] + 1
                ckey1 = ""
                for k in range(self.aoc) :
                    ckey1 = ckey1 + str(ccomm1[k]) + "|"
                if (ckey1 in keymap) :
                    color = keymap[ckey1]
                    new_cc1[color].append(self.cc1[i][j])
                    new_nc1[self.cc1[i][j]] = color
                    self.balances[-1][color] = self.balances[-1][color] + 1
                else :
                    if (aoc != i) :
                        stable = False
                    keymap[ckey1] = aoc
                    new_cc1.append([self.cc1[i][j]])
                    new_nc1[self.cc1[i][j]] = aoc
                    aoc = aoc + 1
                    self.balances[-1].append(1)
            self.keymaps[-1].append(keymap)
        self.cc1 = new_cc1
        self.nc1 = new_nc1
        self.aoc = aoc
        return stable

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
            aoc = old_aoc + 1

            br = False

            not_stable = True
            while (not_stable) :
                balances = []
                not_stable = False
                new_aoc = 0
                new_cc = []
                new_nc = list(nc)
                for i in range(aoc) :
                    for j in range(len(cc[i])) :
                        ccomm = [0 for x in range(aoc)]
                        for k in range(len(self.e2[cc[i][j]])) :
                            ccomm[nc[self.e2[cc[i][j]][k]]] = ccomm[nc[self.e2[cc[i][j]][k]]] + 1
                        ckey = ""
                        for k in range(aoc) :
                            ckey = ckey + str(ccomm[k]) + "|"
                        if (ckey in self.keymaps[y][i]) :
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

    def is_balanced (self):
        if len(self.cc1) != len(self.cc2):
            return False
        for color in range(self.aoc):
            if len(self.cc1[color]) != len(self.cc2[color]):
                return False
        return True

    def isEqual (self) :
        if (self.l1 != self.l2) :
            return False
        for i in range(self.l1) :
            if (len(self.e1[i]) != len(self.e2[i])) :
                return False
            for j in range(len(self.e1[i])) :
                if (self.e1[i][j] != self.e2[i][j]) :
                    return False
        return True

def relable_graph(G):
    t_1 = tuple(map(sorted, zip(*G)))
    min_x, min_y = t_1[0][0], t_1[1][0]
    min_element = min(min_x, min_y)
    temp = np.subtract(G, min_element)
    t_2 = [tuple(x) for x in temp]
    return t_2

def read_graphs_from_files(fp):
    dir_content = os.listdir(path=fp)
    sorted_dir_content = sorted(dir_content)
    for i in range(0,len(sorted_dir_content), 2):
        file_content_1 = open(fp+sorted_dir_content[i])
        file_content_2 = open(fp+sorted_dir_content[i+1])
        t_1 = [line.strip('e ').rstrip() for line in file_content_1]
        temp_1 = t_1[0].split()
        temp_1 = temp_1[2]
        num_nodes_1 = [x for x in range(int(temp_1))]
        t_1 = t_1[1:]
        graph_1 = [tuple(map(int, t.split())) for t in t_1]
        graph_1 = relable_graph(graph_1)
        t_2 = [line.strip('e ').rstrip() for line in file_content_2]
        temp_2 = t_2[0].split()
        temp_2 = temp_2[2]
        num_nodes_1 = [x for x in range(int(temp_2))]
        t_2 = t_2[1:]
        graph_2 = [tuple(map(int, t.split())) for t in t_2]
        graph_2 = relable_graph(graph_2)
        A = nx.Graph()
        A.add_nodes_from(num_nodes_1)
        A.add_edges_from(graph_1)
        B = nx.Graph()
        B.add_nodes_from(num_nodes_1)
        B.add_edges_from(graph_1)
        competition(A, B)

def competition(G, H):
    x = GraphIsoTester(G, H)
    status = x.has_isomorphism()
    # f = open('out', 'a')
    if status == True:
        print('1')
    else:
        print('0')
    # f.close()

folder_path = sys.argv[1]

read_graphs_from_files(folder_path)
