mkdir -p ./output/diagrams/tmp
cd output/diagrams
cp -r ../../book ./tmp
cp -r ../../chapters ./tmp
files=$(find ./tmp/chapters -type f | sort -t '\0' -n)
COUNT=0

function extractTheDiagrams() {
  for fl in $files; do
    temp_file=$(mktemp)
    perl -n0777 -e 'while (/(`{3}mermaid.*?)`{3}/sg) { print $&; print "\nOAOAOAOAO\nBANANA"; }' "$fl" > "$temp_file"
    csplit -z -f "output$COUNT" -n 2 -b '%02d.mmd' $temp_file '/OAOAOAOAO/' '{*}'
    COUNT=$(($COUNT + 1))
    rm -f "$temp_file"
  done
  for out in $(find . -type f -name 'output???.mmd' | sort -t '\0' -n); do
    sed -E 's/OAOAOAOAO//g' -i $out
    sed -E 's/BANANA//g' -i $out
    sed -E 's/`{3}mermaid//g' -i $out
    sed -E 's/`{3}//g' -i $out
    mmdc -i $out -o $out.png -b transparent
  done
  mkdir -p pictures
  cp *.png pictures/
  wslview pictures
}



extractTheDiagrams || echo "Extraction failed"
