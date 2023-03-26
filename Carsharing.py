#!/usr/bin/env python
# coding: utf-8

# In[ ]:


#------------------------------调包-----------------------#
import geopandas as gpd
import pandas as pd
import matplotlib.pyplot as plt
import osmnx as ox
import taxicab as tc  #导入taxicab包
import math
import random
from random import randint
#加载依赖库
import networkx as nx
from networkx.algorithms import approximation         #调用启发式算法的包
import PIL 
import numpy as np
from haversine import haversine
#四个常数，可以测试取最优结果，目前取1
c1=1
c2=1
c3=1
c4=1


# In[ ]:


#获得嘉定区路网图
G1=ox.graph.graph_from_xml(r"sh.osm") #获取嘉定区数据
G1 = ox.projection.project_graph(G1)   #进行投影
G_84 = ox.projection.project_graph(G1,to_crs='EPSG:4326')  


# In[ ]:


#---------------------------------最大权重独立集函数--------------------------#
#初始化生成初始解
def Initialize(G):
    S=[]
    AddFreeNode(S,G)
    return S
            
#求解独立集权重的函数
def Weight(S,G):
    total=0
    if(len(S)):
        for i in S:
            total+=G.nodes[i]['weight']
    return total

#返回V-S的集合
def GET_V_S(S,G):
    V_S=[]
    if(S):
        for i in G.nodes:
            if(i not in S):
                V_S.append(i)
        return V_S
    else:
        return list(G.nodes)
#随机均匀添加节点
#随机均匀添加节点
def AddFreeNode(S,G):
    V_S=GET_V_S(S,G)
    Isend=True
    while(Isend):
        k=randint(0,len(V_S)-1) #随机生成节点
        j=V_S[k]              #j为节点
        if(S==None):
            S.append(j)
            V_S.remove(j)
        else :
            Isadd=True          #判断是否添加节点
            for i in S:
                if((i,j) in G.edges or G.nodes[j]['weight']<0):       #说明节点不独立，或者权重为0，不添加
                    Isadd=False
                    break
            if(Isadd):
                S.append(j)
                V_S.remove(j)
        
        #下列代码为了判断S是否已经是最大集  
        Ending=True
        for i in V_S:
            Iexit=False
            for j in S:
                if((i,j) in G.edges()):
                    Iexit=True               #说明相连
                    break
            if(Iexit==False and G.nodes[i]['weight']>=0):    
                S.append(i)
                V_S.remove(i)
                Ending=False
                break
        if(Ending):
            Isend=False         
#扰动函数
def Perturb(k,S,G):
    S1=S.copy()
    V_S=GET_V_S(S,G)
    Se=[]
    i=0
    while(i<k):
        a=randint(0,len(V_S)-1)
        b=V_S[a]
        if(Se==None):
            Se.append(b)
            i+=1
        elif(b not in Se):
            Notadd=False
            for vertex in Se:
                if((b,vertex) in G.edges):
                    Notadd=True
                    break
            if(not Notadd):
                Se.append(b)
                i+=1
    #进行扰动
    RE=[]  #记录需要删除的元素,不能直接remove，会有bug
    for ve in Se:
        for v in S1:
            if((v,ve) in G.edges()):
                RE.append(v)
    #加入节点
    for v in RE:
        S1.remove(v)
    for v in Se:
        S1.append(v)
    AddFreeNode(S1,G)
    return S1


# In[ ]:


#利用邻域框架添加节点
def Firstimprovement(k,S,G):  #O(n2)
    V_S=GET_V_S(S,G)
    S1=S.copy()
    if k==1:  #w-1交换法:插入1个节点，删除与之相连的w个顶点
        for v in V_S:
            total=0   #记录权重，判断删除后效果
            a=[]  #记录节点
            for k in S1:
                if((v,k) in G.edges):
                    total+=G.nodes[k]['weight']
                    a.append(k)
            #如果权重满足条件的话
            if(G.nodes[v]['weight']-total>0):
                for k in a:
                    if(k in S1):
                        S1.remove(k)
                S1.append(v)
                break
        return S1
    else:         #1-2交换法   删除1个顶点，交换与之相连的顶点——   O(n3)
        for i in S1:
            count=0
            Solution=[]     #先求得可能加入的点集
            T_Solution=[]
            for j in V_S:
                if((i,j) in G.edges):
                    Solution.append(j)
            #找到与i相连的两个顶点,并且这两个与其他顶点不相连
            RE=[]
            for j in S1:
                if(j!=i):
                    for k in Solution:
                        if((k,j) in G.edges):
                            RE.append(k)
            for vertex in RE:
                Solution.remove(vertex)
            #若条件判断后节点不为空
            if(Solution):  #删除节点后不为空
                for k1 in range(len(Solution)):
                    for k2 in range(k1+1,len(Solution)):
                        #k1,k2只是下标，具体的还要得到节点值!!pay attention!
                        k1node=Solution[k1]    
                        k2node=Solution[k2]
                        if(((k1node,k2node) not in G.edges) and ((G.nodes[k1node]['weight']+G.nodes[k2node]['weight'])>=G.nodes[i]['weight'])):
                            T_Solution.append((k1node,k2node))
            #进行加入判断,如果满足权重要求，就加入
            if(T_Solution):
                S1.remove(i)
                S1.append(T_Solution[0][0])
                S1.append(T_Solution[0][1])
                break
        return S1 
#局部搜索算法


#Add FreeNnode in order to make max independent set
def LocalSearch(S,G):
    k=1
    while(k<=2):
        S1=Firstimprovement(k,S,G)    #k=1采用1个插入方式，k=2采用(1,2)交换法 ,也就是两个邻域结构
        if(Weight(S1,G)<=Weight(S,G)):
            k+=1
        else:
            k=1
            S=S1
            AddFreeNode(S,G)          #inorder to make maximum set number
    return S

#接受函数
def Accept(S,S_,S1,i,local_best_w,G):
    if(Weight(S,G)<Weight(S1,G)):
        S=S1
        i=1
        if local_best_w<Weight(S,G):
            local_best_w=Weight(S,G)
            i=i-(len(S)/c2)
        if Weight(S_,G)<Weight(S,G):
            S_=S
            i=i-(len(S)/c3)
    elif(i<=(len(S)/c2)):
        i+=1
    else:
        local_best_w=Weight(S,G)
        S=Perturb(c4,S,G)
        i=1
    return (S,S_,i,local_best_w)
#局部迭代搜索函数
def ILS_VND(G,maxIter):
    '''
    传入图和最大迭代次数
    '''
    global c1,c2,c3,c4
    S0 = Initialize(G) # initial solution
    S = LocalSearch(S0, G) #current solution,通过本地搜索得到一个解
    S_=S
    local_best_w = Weight(S,G)  
    iter = 1
    i = 1
    while iter<maxIter:
        S1=Perturb(c1,S,G)       #扰动解决方案
        S1 = LocalSearch(S1, G)
        (S, S_, i, local_best_w) = Accept(S, S_, S1, i, local_best_w, G)
        iter = iter + 1
    return S_
#----------------------------------------------End---------------------------------------------#

