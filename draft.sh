mkdir -p ./output
cd output
files="../book/cover.md $(find ../chapters -type f | sort -t '\0' -n | tr '\n' ' ')"
fileName="whitepaper"

function generate() {
  pandoc \
    $files \
    -o "./$fileName.$1" \
    -V colorlinks=true \
    -V linkcolor=blue \
    -V toccolor=gray \
    -F mermaid-filter
    #--pdf-engine=xelatex \
    #--variable mainfont="DejaVu Serif" \
    #--variable sansfont="DejaVu Serif"

}

generate "pdf"
generate "epub"
generate "html"

wslview "./$fileName.pdf"
