mkdir -p ./output
cd output
files="../book/cover.md $(find ../chapters -type f | sort -t '\0' -n | tr '\n' ' ')"
bookTitle="Book template"
fileName="book template"

function generate() {
    pandoc \
    $files \
    -o ".$fileName.$1" \
    -V colorlinks=true \
    -V linkcolor=blue \
    -V toccolor=gray \
    --metadata title="$bookTitle"
}

generate "pdf"
generate "epub"

wslview ".$fileName.pdf"
