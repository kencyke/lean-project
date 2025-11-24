FROM mcr.microsoft.com/devcontainers/base:noble

ARG USERNAME="vscode"

RUN SNIPPET="export PROMPT_COMMAND='history -a' && export HISTFILE=/commandhistory/.bash_history" \
    && mkdir /commandhistory \
    && touch /commandhistory/.bash_history \
    && chown -R $USERNAME /commandhistory \
    && echo "$SNIPPET" >> "/home/$USERNAME/.bashrc"

RUN apt-get update && \
    apt install -y ripgrep

USER vscode
WORKDIR /home/vscode

RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:4.25.1
ENV PATH="/home/vscode/.elan/bin:${PATH}"
