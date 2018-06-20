#!/bin/bash
find posts/ -name "*$1*.markdown" | while read -r line ; do
  filename=$(echo "$line" | cut -c19-)
  mv "$line" "drafts/$filename"
done

