#!/bin/bash

# 定义输入和输出目录
INPUT_DIR="./compare_to_mlir"
OUTPUT_DIR="./mlir"

# 创建输出目录（如果不存在）
mkdir -p "$OUTPUT_DIR"

# 遍历输入目录下的所有 .fir 文件
for file in "$INPUT_DIR"/*.fir; do
    # 检查文件是否存在（避免无匹配文件时报错）
    if [ -f "$file" ]; then
        # 提取文件名
        filename=$(basename "$file")
        output_path="$OUTPUT_DIR/$filename"

        # 删除仅包含 { 或 } 的行（允许前后空白）
        # 使用 [[:space:]] 兼容所有 sed 版本，也可用 \s（GNU sed）
        sed '/^[[:space:]]*{[[:space:]]*$/d; /^[[:space:]]*}[[:space:]]*$/d' "$file" > "$output_path"

        echo "已处理: $file -> $output_path"
    fi
done

echo "所有文件处理完成。"
