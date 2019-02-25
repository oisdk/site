#!/bin/bash
find drafts -name "*$1*.markdown" | while read -r line ; do
  filename=$(echo "$line" | cut -c8-)
  mv "$line" "posts/$(date +%Y-%m-%d)-$filename"
done
