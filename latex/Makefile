# Main document file
MAIN = main
TEX_FILE = $(MAIN).tex
OUTPUT_DIR = output
PDF_FILE = $(OUTPUT_DIR)/$(MAIN).pdf

# LaTeX compiler
LATEX = pdflatex

all: $(PDF_FILE) ## Compile the LaTeX document to PDF

help: ## Show this help message
	@echo "Available targets:"
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "  %-15s %s\n", $$1, $$2}'

$(OUTPUT_DIR):
	mkdir -p $(OUTPUT_DIR)

$(PDF_FILE): $(TEX_FILE) references.bib | $(OUTPUT_DIR)
	$(LATEX) -output-directory=$(OUTPUT_DIR) $(TEX_FILE)
	bibtex $(OUTPUT_DIR)/$(MAIN)
	$(LATEX) -output-directory=$(OUTPUT_DIR) $(TEX_FILE)
	$(LATEX) -output-directory=$(OUTPUT_DIR) $(TEX_FILE)

clean: ## Remove auxiliary LaTeX files
	rm -f $(OUTPUT_DIR)/*.aux $(OUTPUT_DIR)/*.log $(OUTPUT_DIR)/*.out $(OUTPUT_DIR)/*.toc $(OUTPUT_DIR)/*.lof $(OUTPUT_DIR)/*.lot $(OUTPUT_DIR)/*.bbl $(OUTPUT_DIR)/*.blg $(OUTPUT_DIR)/*.idx $(OUTPUT_DIR)/*.ind $(OUTPUT_DIR)/*.ilg $(OUTPUT_DIR)/*.glo $(OUTPUT_DIR)/*.gls $(OUTPUT_DIR)/*.glg $(OUTPUT_DIR)/*.ist $(OUTPUT_DIR)/*.fls $(OUTPUT_DIR)/*.fdb_latexmk $(OUTPUT_DIR)/*.synctex.gz

distclean: clean ## Remove all files including PDF
	rm -f $(OUTPUT_DIR)/$(MAIN).pdf
	rmdir $(OUTPUT_DIR) 2>/dev/null || true

rebuild: distclean all ## Clean and rebuild everything

.PHONY: all clean distclean rebuild help
