// Keep the runtime pinned so local previews and published books typeset alike.
window.MathJax = {
    tex: {
        inlineMath: [['\\(', '\\)']],
        displayMath: [['\\[', '\\]']],
    },
    output: {
        displayAlign: 'left',
        // Authored rules supply their own line breaks; the enclosing block scrolls.
        displayOverflow: 'overflow',
    },
};

const mathjaxScript = document.createElement('script');
mathjaxScript.id = 'MathJax-script';
mathjaxScript.src = 'https://cdn.jsdelivr.net/npm/mathjax@4.1.3/tex-chtml.js';
mathjaxScript.async = true;
document.head.appendChild(mathjaxScript);
