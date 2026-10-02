#!/bin/sh
# Render every scene of pivot.py at 1080p60 and join them into pivot.mp4.
# Needs Manim Community (pip install manim), LaTeX with dvisvgm, and ffmpeg.
set -e
cd "$(dirname "$0")"
PY=${PYTHON:-python3}
SCENES="Title Multiplexor Angle Path Alpha Beta Merge"
for s in $SCENES; do
  "$PY" -m manim -qh --disable_caching pivot.py "$s"
done
: > scenes.txt
for s in $SCENES; do echo "file 'media/videos/pivot/1080p60/$s.mp4'" >> scenes.txt; done
ffmpeg -y -loglevel error -f concat -safe 0 -i scenes.txt -c copy pivot.mp4
rm scenes.txt
echo "wrote $(pwd)/pivot.mp4"
