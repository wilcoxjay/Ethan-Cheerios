all: blog_comparison.html

%.md: %.v
	python3 ../coq-lit/coq-lit.py -weave $< > $@

%.html: %.md
	pandoc -f markdown-markdown_in_html_blocks -H coqlit.header --mathjax -c style.css -c blog-post.css -s $< -o $@


.PHONY: all
