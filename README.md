# Book template
The `pdf-dependencies.sh` has the packages needed in Ubuntu to generate the output file.
End all your .md files with double white lines in the end or the markdown will merge with the one in the next chapter.

For the puppeteer issues in WSL:
cd /tmp
sudo wget https://dl.google.com/linux/direct/google-chrome-stable_current_amd64.deb
sudo dpkg -i google-chrome-stable_current_amd64.deb
sudo apt install --fix-broken -y
sudo dpkg -i google-chrome-stable_current_amd64.deb
