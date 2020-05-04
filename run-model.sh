echo "------------------------------------------------------------------------------------"
echo "A.cfg"
cat A.cfg
echo "------------------------------------------------------------------------------------"
tlc -dump dot images/A.dot -config A.cfg rcsp.tla && dot -Tpng images/A.dot -o images/A.png


echo "------------------------------------------------------------------------------------"
echo "B.cfg"
cat B.cfg
echo "------------------------------------------------------------------------------------"
tlc -dump dot images/B.dot -config B.cfg rcsp.tla && dot -Tpng images/B.dot -o images/B.png


echo "------------------------------------------------------------------------------------"
echo "C.cfg"
cat C.cfg
echo "------------------------------------------------------------------------------------"
tlc -dump dot images/C.dot -config C.cfg rcsp.tla && dot -Tpng images/C.dot -o images/C.png
