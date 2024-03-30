# Tai-e-Assignment

Tai-e 学习记录
博客地址：https://blog.csdn.net/qsort_/article/details/130760134

# 0x01 活跃变量分析和迭代求解器

第一题可以算作一道让学生来熟悉 tai-e 平台的签到题，因为具体实现算法在课程中已经讲到了，所以只需要按照作业中的提示，完成每个函数就行了。但是对于很久没做过 java 开发的同学来说，在实现 transferNode 方法的时候，可能会犯下面的低级错误：
计算 OUT[B] - def[B]的值时，直接调用了 out.remove(def)方法，这时虽然 IN 的值算出来了，但是 OUT 的值却被修改了，因此在最开始，需要使用 out.copy()方法拷贝一份 out 的值，然后调用拷贝对象的 remove(def)方法就可以了。

# 0x02 常量传播和 Worklist 求解器

这一题是分析整数类型的常量传播，题目对要程序要分析的范围划分也很明确，因此在实现 transferNode 方法时，仅分析 DefinitionStmt 语句就可以了。这道题应该是我花费时间最多的一道题，一度因为一个测试用例而 WA，直到考虑了下面这个条件才 AC：
对于除以 0 的情况（出现在 / 和 % 中），无论被除数是 NAC，还是其他什么值，他的结果都应该是 UNDEF。

# 0x03 死代码检测

做这道题时，比较难处理的是 SwitchStmt，因此我们需要先去了解 switch 语法在 IR 和 cfg 中的表现形式，相信有了前两道题的经验，大家应该也知道了 IR 文件都在 sootOutput 文件夹下，cfg 会被输出到 output 文件夹下，后缀是.dot，需要借助 Graphviz 工具，使用 dot -Tpng xxx.dot -O 命令即可将.dot 文件转换为 png 来查看，但前提是需要把 pascal.taie.analysis.Tests#DUMP_CFG 这个属性设置为 true。相信大家借助 cfg 图，就会有处理 SwitchStmt 的思路了。

# 0x04 类层次结构分析与过程间常量传播

这道题实现起来比较简单的是实现类层次结构分析，比较难的是实现过程间常量传播。但最后发现，过程间常量传播只是需要花点精力来处理那 4 种类型的边，只要把算法设计出来，测试用例可以一把过，反而 oj 上的类层次结构分析的测试用例，却一直没通过，后来通过查看 tai-e 提供的 api，最终是 AC 了，情况是这样的：

1、开始我没注意到 DefaultCallGraph 类有 addReachableMethod 方法，但是我注意到了他有 reachableMethods 这个属性，因此我就用这个属性保存了我找到的 reachableMethod，然后通过遍历这个方法里所有的 stmt，来获取所有的 callSite，最终实现了整个算法，我手动实现的这个算法的结果肯定是没问题的，要不常量传播的测试用例不可能通过。但是在 oj 上，我所有的类层次结构分析的测试用例都没通过。
2、后来我改用了 addReachableMethod 方法来保存 reachableMethod，跟进这个方法我发现他的实现跟我一样，而且他顺带也保存了方法里所有的 callSite，所以直接用 callGraph.callSitesIn(m)方法就可以获取 m 方法中所有的 callSite，用这个方法最终通过了 oj 上所有测试用例。

# 0x05 指针分析

无论是非上下文敏感的指针分析，还是上下文敏感的指针分析，课程中讲的都非常清晰，因此只要把课程完整跟下来，充分理解了具体的算法，基本上都可以一次性 AC，这里也没啥坑点，就不多说了。

# 0x06 Alias-Aware 的过程间常量传播

同上，这道题只要把作业中的描述都理解了，理解了什么是别名，然后按照作业的指引，正确处理 LoadField、LoadArray、StoreField、StoreArray 这 4 种 stmt 就可以了。
不过可以在 initialize 方法中提前保存一下每个变量的别名，以及所有静态的 StoreField，和所有静态的 LoadField，方便后面使用。当然这也不是必须的，也可以在后面需要这些信息的时候再实时计算，不过这种方式效率会很低。

# 0x07 污点分析

最后一个作业，花费了很长时间在算法设计上。
1、Sources 规则比较好处理，在指针分析里合适的地方插进去就行了。
2、TaintTransfers 规则同样也是需要在指针分析里合适的地方进行处理。但是这里处理的结果该怎么保存呢？这里想了很久，最终想到需要用一个图来建立污点传播的关系。这个图的数据结构可以参考 PointerFlowGraph。基于污点流图，就可以在指针流图上进行污点传播了。需要注意的是，在传播污点数据时，只传播污点对象就行了，不要把普通的指针分析的对象也给传播了。
3、根据作业中给的提示，可以在 collectTaintFlows()方法中实现处理 Sinks 的规则。这时遍历程序所有 callSite 即可。当然也可以在 TaintAnalysiss 类中提供一个方法，用来保存所有符合 Sink 规则的 callSite，然后插在指针分析的合适的位置，最后遍历这些 callSite 就行了，这样可能更高效些。
