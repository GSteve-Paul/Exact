echo "*** QUBO ***"
python3 qubo/qubo.py qubo/bqp50.1
echo ""

echo "*** GRAPH COLORING ***"
python3 graph_coloring/graph_coloring.py graph_coloring/graph_77v-7chrom_adj_matrix.txt 4 graph_coloring/graph_77v-7chrom_symmetries.txt 0
echo ""

echo "*** KNAPSACK CLASSIC ***"
python3 knapsack_tutorial/1_classic_knapsack.py
echo ""

echo "*** KNAPSACK IMPLICATIONS LOW LEVEL ***"
python3 knapsack_tutorial/2_implications_low_level.py
echo ""

echo "*** KNAPSACK IMPLICATIONS SIMPLE ***"
python3 knapsack_tutorial/3_implications_simple.py
echo ""

echo "*** KNAPSACK ASSUMPTIONS ***"
python3 knapsack_tutorial/4_assumptions.py
echo ""

echo "*** KNAPSACK ONEHOT ***"
python3 knapsack_tutorial/5_onehot.py
echo ""

echo "*** COUNT ***"
python3 count.py
echo ""

echo "*** NO THREE IN LINE ***"
python3 no_three_in_line.py
echo ""

echo "*** PROOF LOGGING ***"
python3 proof_logging.py
echo ""

echo "*** RAMSEY ***"
python3 ramsey.py
echo ""


