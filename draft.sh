mkdir -p ./output/tmp
cd output
cp -r ../book ./tmp
cp -r ../chapters ./tmp
cp -r ../images ./tmp

for fl in $(find ./tmp/chapters -type f)
do
  content=$(cat $fl)
  echo $'\\pagebreak' > $fl
  echo "$content" >> $fl
  sed -E 's/\]\(\.[^\.]*\.md#/](#/g' -i $fl
done

files="./tmp/book/cover.md $(find ./tmp/chapters -type f | sort -t '\0' -n | tr '\n' ' ')"
fileName="whitepaper"

function generate() {
  pandoc \
    $files \
    -o "./$fileName.$1" \
    -V colorlinks=true \
    -V linkcolor=blue \
    -V toccolor=gray \
    -F mermaid-filter
}

generate "pdf"

rm -rf ./tmp

wslview "./$fileName.pdf"
