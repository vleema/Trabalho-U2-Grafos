FROM texlive/texlive:latest

WORKDIR /latex

# Copy all files from the latex directory
COPY . .

# Compile the LaTeX document
RUN make all

# The compiled PDF will be in /latex/output/main.pdf
CMD ["cat", "output/main.pdf"]
