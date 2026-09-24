import numpy as np
import os
import pandas as pd
import plotly.express as px
import re
import status_counts
import subprocess
from datetime import datetime

conf = {
    'line_colors': ['#4285F4'],
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
    'out_path_prefix': 'site/data/file_counts'
}

status_conf = dict(
    conf,
    # Same dimensions and starting point as the file count, only the series and
    # where they are written differ.
    line_colors=['#EA4335', '#34A853', '#4285F4'],
    title=dict(
        text='Statements by status in Formal Conjectures',
        font=dict(size=18),
        x=0.5,
        xanchor='center'
    ),
    ylabel=['Open', 'Solved', 'Formally proved'],
    yaxis_title='Statement Count',
    out_path_prefix='site/data/status_counts'
)

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

def plot_counts(
      df,
      xlabel,
      ylabel,
      max_width,
      width_pct,
      height,
      line_colors,
      line_width,
      title,
      out_path,
      theme,
      yaxis_title=None):
    """
    Plots one or more counts over time.

    Args:
        df (pd.DataFrame): A pandas DataFrame which should contain `xlabel` and `ylabel` as columns
        xlabel (str): The column from `df` to use as the `x`-axis
        ylabel (str | list[str]): The column(s) from `df` to use as the `y`-axis
        max_width (int): Maximum width of plot in `px`
        width_pct (str): % width of plot inside parent div
        height (int): Height of plot in `px`
        line_colors (list[str]): Colour of each plotted graph, in order
        line_width (float): Width of plotted line in `px`
        title (dict): Dictionary specifying graph title and style
        out_path (str): Save location of html
        theme (str): plotly template suffix to use as plot theme. E.g., use "dark" for "plotly_dark"
        yaxis_title (str): Label of the `y`-axis, required when `ylabel` names several columns
    """
    out_path = f"{out_path}_{theme}.html"
    fig = px.line(df, xlabel, ylabel, color_discrete_sequence=line_colors)

    fig.update_layout(
        title=title,
        template=f"plotly_{theme}",
        hovermode='x unified',
        margin=dict(l=40, r=40, t=60, b=40),
        autosize=True
    )

    fig.update_yaxes(rangemode='tozero')

    fig.update_traces(
        line=dict(width=line_width, shape='hv'),
        marker=dict(size=6)
    )

    if isinstance(ylabel, list):
        # For several columns `px` names the axis "value" and the legend
        # "variable", neither of which says anything to a reader.
        fig.update_layout(yaxis_title=yaxis_title, legend_title_text='')

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

    status_columns = [status_conf['xlabel']] + status_conf['ylabel']
    status_df = pd.DataFrame(
        status_counts.get_status_counts_over_time(
            status_conf['start_date'], status_columns),
        columns=status_columns)

    # The last point should agree with the counts `extract_names` reports, so
    # print it where a mismatch is visible without opening the site.
    latest = status_df.iloc[-1]
    print('Latest statement counts: ' +
          ', '.join(f'{label} {latest[label]}' for label in status_conf['ylabel']))

    for settings, data in [(conf, df), (status_conf, status_df)]:
        for theme in ["white", "dark"]:
            plot_counts(
              df=data,
              xlabel=settings['xlabel'],
              ylabel=settings['ylabel'],
              max_width=settings['max_width'],
              width_pct=settings['width_pct'],
              height=settings['height_px'],
              line_colors=settings['line_colors'],
              line_width=settings['line_width'],
              title=settings['title'],
              out_path=settings['out_path_prefix'],
              theme=theme,
              yaxis_title=settings.get('yaxis_title')
            )
