import os
import re

# A set of common Lean declaration keywords.
DECLARATION_KEYWORDS = {
    'theorem', 'def', 'lemma', 'axiom', 'example', 'inductive',
    'structure', 'class', 'instance', 'abbrev', 'opaque', 'constant'
}

def is_start_of_code_block(line: str) -> bool:
    """
    Checks if a line is the start of a declaration or a doc-comment (`/--`).
    This helps find the correct place to insert the namespace.
    We ignore empty lines and regular comments (`--`).
    """
    stripped_line = line.strip()
    # Ignore blank lines or regular comments
    if not stripped_line or stripped_line.startswith('--'):
        return False

    # A doc-comment is a valid start
    if stripped_line.startswith('/--'):
        return True

    # Any declaration keyword is a valid start
    if any(stripped_line.startswith(keyword) for keyword in DECLARATION_KEYWORDS):
        return True

    return False

def process_lean_file(filename: str):
    """
    Checks a .lean file and adds a namespace if it's missing,
    correctly handling doc-comments.

    Args:
        filename (str): The name of the file to process.
    """
    # 1. Check if the filename matches the "n.lean" pattern.
    match = re.match(r'^(\d{1,3})\.lean$', filename)
    if not match:
        return

    file_number = match.group(1)
    namespace_start = f'namespace Erdos{file_number}'
    namespace_end = f'end Erdos{file_number}'

    try:
        with open(filename, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except Exception as e:
        print(f"❌ Error reading {filename}: {e}")
        return

    # 2. Check if the namespace already exists.
    if any(namespace_start in line for line in lines):
        print(f"ℹ️ Namespace already exists in {filename}. Skipping.")
        return

    # 3. Find the index of the first declaration or its preceding doc-comment.
    insertion_index = -1
    for i, line in enumerate(lines):
        if is_start_of_code_block(line):
            insertion_index = i
            break

    # 4. If a valid insertion point was found, modify the file content.
    if insertion_index != -1:
        # Prepare the lines to insert for clean formatting.
        # Add a blank line before the namespace if the preceding line isn't already blank.
        prefix = '\n' if insertion_index > 0 and lines[insertion_index-1].strip() else ''

        # Insert the 'namespace' line.
        lines.insert(insertion_index, f'{prefix}{namespace_start}\n\n')

        # Add the 'end' line, ensuring there's a blank line before it.
        if lines[-1].strip(): # If the last line has content...
             lines.append('\n') # ...add a separating newline.
        lines.append(f'{namespace_end}\n')

        # 5. Write the modified content back to the file.
        try:
            with open(filename, 'w', encoding='utf-8') as f:
                f.writelines(lines)
            print(f"✅ Successfully updated {filename}.")
        except Exception as e:
            print(f"❌ Error writing to {filename}: {e}")
    else:
        print(f"⚠️ No declaration found in {filename}. Skipping.")


def main():
    """
    Main function to traverse the current directory and process files.
    """
    print("Starting script to add namespaces to .lean files...")
    current_directory = os.getcwd()

    for filename in os.listdir(current_directory):
        if filename.endswith('.lean'):
            process_lean_file(filename)
    print("\nScript finished.")


if __name__ == "__main__":
    main()
