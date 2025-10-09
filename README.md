# Chew's Tech Blog

Welcome to the repository for my personal technical blog! This site is built with Jekyll and hosted on GitHub Pages. Here, I write about my journey and interests in computer science.

**[Visit the live blog &rarr;](https://excitedspider.github.io/)**

## 📚 About This Blog

This blog serves as my digital notebook where I share articles and notes on topics that I'm passionate about, including:

- **Programming Language Theory & Formal Methods**: Exploring the theoretical foundations of programming languages, with notes on Abstract Interpretation and using proof assistants like Coq.
- **Natural Language Processing (NLP)**: Diving into concepts like N-Grams and Language Models.
- **C++**: Sharing insights on modern C++ features, such as object life cycles and runtime polymorphism.
- **Distributed Systems**

You can learn more about me on my **[About Page](httpss://excitedspider.github.io/about/)**.

## 🛠️ Built With

This blog is built using a simple and robust stack, leveraging the GitHub ecosystem for development and deployment.

- **[Jekyll](https://jekyllrb.com/)**: A static site generator that transforms plain text into a static website.
- **[Ruby](https://www.ruby-lang.org/en/)**: The language powering Jekyll.
- **[GitHub Pages](https://pages.github.com/)**: For hosting the static site directly from this repository.
- **[GitHub Actions](https://github.com/features/actions)**: For continuous integration and deployment. Every push to the `master` branch automatically builds the site and deploys it.

## 🚀 Getting Started

You can run a local copy of this blog for development or to preview changes.

### Prerequisites

You'll need a working Ruby development environment. You can follow the official Jekyll installation guide to set it up for your operating system.

### Installation & Local Server

1.  **Install system dependencies (on Fedora):**
    You'll need Ruby development headers and build tools to install the Jekyll gems.
    
    For example, if you are using Fedora:
    ```bash
    sudo dnf install ruby-devel gcc gcc-c++ make glibc-headers glibc-devel
    ```

2.  **Clone the repository:**
    ```bash
    git clone https://github.com/ExcitedSpider/excitedspider.github.io.git
    cd excitedspider.github.io
    ```

3.  **Install Ruby dependencies:**
    This project uses `bundler` to manage Ruby gems.
    ```bash
    bundle install
    ```

4.  **Run the Jekyll server:**
    This command builds the site and serves it locally. It will also watch for changes and automatically regenerate the site.
    ```bash
    bundle exec jekyll serve
    ```

5.  **View the blog:**
    Open your browser and navigate to `http://127.0.0.1:4000`.

## ✒️ How to Add a New Post

1.  Create a new Markdown file in the `_posts` directory.
2.  Follow the Jekyll naming convention: `YYYY-MM-DD-your-post-title.md`.
3.  Add the necessary front matter at the top of the file (e.g., `layout`, `title`, `categories`, `description`).
4.  Write your content in Markdown.
5.  Commit and push to the `master` branch. GitHub Actions will handle the rest!

## 📫 Contact

If you'd like to connect, feel free to reach out to me via LinkedIn or email at <chew.y.feng@outlook.com>.
