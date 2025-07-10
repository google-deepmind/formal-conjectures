import numpy as np
import os
import pandas as pd
import plotly.express as px
import re
import subprocess
from datetime import datetime, timedelta

conf = {
  'line_color': '#4285F4', # Color used in plotting
  'line_width': 3, # Width of line used in the plot
  'title': dict(
    text='Number of Lean files in Formal Conjectures', # Title text
    font=dict(size=15), # Title font
    x=0.5, # Center title
    xanchor='center' # Center title
  ),
  'max-width': '1000px', # Width of plot in px
  'aspect-ratio': 2, # aspect ratio of plot
  'start_date': '2025-05-28', # Announcement date is '2025-05-28'
  'xlabel': 'Date', # x-axis label on plot
  'ylabel': 'Number of Lean files', # y-axis label on plot
  'out_path': 'docbuild/out/file_counts.html' # This is used as an arg to overwrite_index.lean in .github/workflows/build-and-docs.yml
}

def get_file_counts_over_time(start_date, columns):
    """
    Retrieves file counts over time

    Args:
        start_date (str): Date from which to start collecting commits
        columns (list[str]): Column labels for the returned df, should of length 2

    Returns:
        pd.DataFrame: A DataFrame with dates as the first column and file counts as the second
    """
    if not isinstance(columns, list) or len(columns) != 2:
      raise ValueError("The `columns` parameter should be a list of length 2.")

    data = []

    command = ['git', 'log',  '--pretty=format:%H,%ct']
    result = subprocess.run(command, capture_output=True, text=True, check=True)
    commit_lines = result.stdout.strip().split('\n')

    # Filter out any empty lines
    commit_lines = [line for line in commit_lines if line]

    # Process commits
    for line in commit_lines:
        # Extract sha and timestamp
        sha, timestamp = line.split(',')
        timestamp = int(timestamp)
        # Only timestamps from `start_date`
        if timestamp > datetime.fromisoformat(start_date).timestamp():
          # Get the number of files in the current commit's tree
          tree_command = ['git', 'ls-tree', '-r', '--name-only', sha]
          tree_result = subprocess.run(tree_command, capture_output=True, text=True, check=True)
          files = tree_result.stdout.strip().split('\n')

          # Only care about lean files in `FormalConjectures` subdir
          subdir_pattern = re.compile(r'^FormalConjectures/.*\.lean')

          file_count = len([f for f in files if f and subdir_pattern.match(f)])
          data.append([datetime.fromtimestamp(timestamp), file_count])

    return pd.DataFrame(data, columns=columns)

def plot_file_counts(df, xlabel, ylabel, max_width, aspect_ratio, line_color, line_width, title, out_path):
    """
    Plots the number of files over time.

    Args:
        df (pd.DataFrame): A pandas DataFrame which should contain `xlabel` and `ylabel` as columns
        xlabel (str): The column from `df` to use as the `x`-axis
        ylabel (str): The column from `df` to use as the `y`-axis
        line_color (str): Colour of plotted graph
        title (dict): Dictionary specifying graph title and style
        out_path (str): Save location of html
    """
    fig = px.line(df, xlabel, ylabel)
    fig.update_layout(title=title)
    fig.update_yaxes(
       scaleanchor="x",
       scaleratio=0.5
    )
    fig.update_traces(line_color=line_color, line_width=line_width)
    fig_html = f"<div style='max-width: {max_width}; aspect-ratio: {aspect_ratio};'> {
       fig.to_html(full_html=False, include_plotlyjs='cdn')} </div>"
    with open(out_path, "w") as f:
       f.write(fig_html)

if __name__ == "__main__":
    github_url = "https://github.com/google-deepmind/formal-conjectures"
    print(f"Generating growth plots for: {github_url}")

    columns = [conf['xlabel'], conf['ylabel']]
    df = get_file_counts_over_time(conf['start_date'], columns)
    plot_file_counts(
      df=df,
      xlabel=conf['xlabel'],
      ylabel=conf['ylabel'],
      max_width=conf['max-width'],
      aspect_ratio=conf['aspect-ratio'],
      line_color=conf['line_color'],
      line_width=conf['line_width'],
      title=conf['title'],
      out_path=conf['out_path']
    )
