FROM rocq/rocq-prover:9.2

# 元イメージは ENTRYPOINT の `opam exec --` で PATH を通しているが、
# devcontainer は ENTRYPOINT を上書きするので、ここで明示的に通しておく
ENV PATH=/home/rocq/.opam/4.14.2+flambda/bin:$PATH

USER root

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
  ca-certificates \
  curl \
  git \
  jq \
  sudo \
  && curl -fsSL https://deb.nodesource.com/setup_24.x | bash - \
  && apt-get install -y --no-install-recommends nodejs \
  && apt-get clean && rm -rf /var/lib/apt/lists/*

RUN echo "rocq ALL=(root) NOPASSWD:ALL" > /etc/sudoers.d/rocq && chmod 0440 /etc/sudoers.d/rocq

# npm install -g を非rootユーザーで実行できるようにする
RUN mkdir -p /usr/local/share/npm-global && chown -R rocq:rocq /usr/local/share/npm-global
ENV NPM_CONFIG_PREFIX=/usr/local/share/npm-global
ENV PATH=$PATH:/usr/local/share/npm-global/bin

USER rocq

# VsRocq 拡張が使う言語サーバー(vsrocqtop)
RUN opam update -y \
&& opam install -y vsrocq-language-server \
&& opam clean -a -c -s --logs

RUN mkdir -p /home/rocq/.claude
RUN npm install -g @anthropic-ai/claude-code
