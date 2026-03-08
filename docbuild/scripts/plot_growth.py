import numpy as np
import os
import pandas as pd
import plotly.express as px
import re
import subprocess
from datetime import datetime

conf = {
    'line_color': '#4285F4',
    'line_width': 2,
    'title': dict(
        text='Number of Lean files in Formal Conjectures',
        font=dict(size=18),
        x=0.5,
        xanchor='center'
    ),
    'width_pct': '90%',
    'height_px': 675,
    'max_width' : 1200, # 16:9 aspect ratio at max
    'start_date': '2025-05-28',
    'xlabel': 'Date',
    'ylabel': 'File Count',
    'out_path_prefix': 'docbuild/out/file_counts'
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
          subdir_pattern = re.compile(r'^FormalConjectures/(?!ForMathlib/).*\.lean')

          file_count = len([f for f in files if f and subdir_pattern.match(f)])
          data.append([datetime.fromtimestamp(timestamp), file_count])

    return pd.DataFrame(data, columns=columns)

def plot_file_counts(
      df,
      xlabel,
      ylabel,
      max_width,
      width_pct,
      height,
      line_color,
      line_width,
      title,
      out_path,
      theme):
    """
    Plots the number of files over time.

    Args:
        df (pd.DataFrame): A pandas DataFrame which should contain `xlabel` and `ylabel` as columns
        xlabel (str): The column from `df` to use as the `x`-axis
        ylabel (str): The column from `df` to use as the `y`-axis
        max_width (int): Maximum width of plot in `px`
        width_pct (str): % width of plot inside parent div
        height (int): Height of plot in `px`
        line_color (str): Colour of plotted graph
        line_width (float): Width of plotted line in `px`
        title (dict): Dictionary specifying graph title and style
        out_path (str): Save location of html
        theme (str): plotly template suffix to use as plot theme. E.g., use "dark" for "plotly_dark"
    """
    out_path = f"{out_path}_{theme}.html"
    fig = px.line(df, xlabel, ylabel)

    fig.update_layout(
        title=title,
        template=f"plotly_{theme}",
        hovermode='x unified',
        margin=dict(l=40, r=40, t=60, b=40),
        autosize=True
    )

    fig.update_traces(
        line=dict(color=line_color, width=line_width, shape='hv'),
        marker=dict(size=6)
    )

    fig_html = fig.to_html(
        full_html=False,
        include_plotlyjs='cdn',
        config={'responsive': True}
    )

    styled_html = f"""
        <style>
            .plot-container {{
                width: {width_pct};
                max-width: {max_width}px;
                height: {height}px;
                margin: 0 auto;
                padding: 10px;
            }}
        </style>

        <div class="plot-container">
            {fig_html}
        </div>
    """

    with open(out_path, "w") as f:
       f.write(styled_html)

if __name__ == "__main__":
    github_url = "https://github.com/google-deepmind/formal-conjectures"
    print(f"Generating growth plots for: {github_url}")

    columns = [conf['xlabel'], conf['ylabel']]
    df = get_file_counts_over_time(conf['start_date'], columns)
    for theme in ["white", "dark"]:
        plot_file_counts(
          df=df,
          xlabel=conf['xlabel'],
          ylabel=conf['ylabel'],
          max_width=conf['max_width'],
          width_pct=conf['width_pct'],
          height=conf['height_px'],
          line_color=conf['line_color'],
          line_width=conf['line_width'],
          title=conf['title'],
          out_path=conf['out_path_prefix'],
          theme=theme
        )
