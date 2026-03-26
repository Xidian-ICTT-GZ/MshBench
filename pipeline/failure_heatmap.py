import matplotlib.pyplot as plt
import numpy as np

models = ["Claude-Opus-4.5", "Qwen3-Max", "DeepSeek-V3.2", "GPT-5.2"]

error_types = ["F1", "F2", "F3", "F4", "F5", "F6"]

data = np.array([
    [12, 3, 7, 0, 6, 88],
    [0, 0, 0, 0, 2, 114],
    [9, 1, 9, 3, 1, 93],
    [13, 1, 9, 0, 3, 90]
])

fig, ax = plt.subplots(figsize=(3.5, 2.4))

bar_width = 0.12
x = np.arange(len(models))

for i in range(len(error_types)):
    ax.bar(x + i * bar_width, data[:, i], width=bar_width, label=error_types[i])

ax.set_xlabel("Model", fontsize=9)
ax.set_ylabel("Number of Failures", fontsize=9)

ax.set_xticks(x + bar_width * 2.5)
ax.set_xticklabels(models, rotation=25, fontsize=8)

ax.tick_params(axis='y', labelsize=8)

ax.grid(axis='y', linestyle='--', linewidth=0.5, alpha=0.7)

ax.legend(
    title="Failure Type",
    fontsize=7,
    title_fontsize=8,
    loc="upper left",
    ncol=3
)

plt.tight_layout()

plt.savefig("failure_types_grouped_bar.pdf", bbox_inches="tight")

plt.show()