#!/bin/bash

# 输出文件
OUTPUT_FILE="output.out"

# 清空（或创建）输出文件
> "$OUTPUT_FILE"

# 遍历所有 .fir 文件
for fir_file in ./compare_to_mlir/*.fir; do
    # 检查是否存在匹配的文件（避免空列表时直接执行）
    if [ -f "$fir_file" ]; then
        echo "Processing: $fir_file" >> "$OUTPUT_FILE"
        ./_build/default/hipparser.exe "$fir_file" >> "$OUTPUT_FILE" 2>&1
        echo "" >> "$OUTPUT_FILE"   # 添加空行分隔不同文件的输出
    fi
done

echo "Done. Results saved to $OUTPUT_FILE"
