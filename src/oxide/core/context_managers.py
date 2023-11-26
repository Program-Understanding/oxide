import contextlib
import builtins
import sys
import shutil
import platform
import logging

NAME = "localstore"
logger = logging.getLogger(NAME)


def getch() -> int:
    """
    Gets a single character from standard input. Does not echo to the screen.
    """
    current_os = platform.system()
    if current_os == 'Windows':
        import msvcrt
        res = msvcrt.getch().decode()
        return res
    else:
        import tty
        import termios
        fd = sys.stdin.fileno()
        old_settings = termios.tcgetattr(fd)
        try:
            tty.setraw(fd)
            ch = sys.stdin.read(1)
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old_settings)
        return ch


@contextlib.contextmanager
def paginated_print_context(page_size=48):
    output_buffer = []  # Buffer to capture output

    # Custom print function to capture output
    def custom_print(*args, **kwargs):
        output_buffer.append(' '.join(map(str, args)))

    # Save the original print function
    original_print = builtins.print

    # Overwrite the built-in print with the custom print
    builtins.print = custom_print

    try:
        yield
    finally:
        # Restore the original print function
        builtins.print = original_print

        # Function to paginate output with less-like controls
        def paginate_output(output, size: int):
            if size <= 0:
                logger.debug('Paginated print had size less than 0 (%d)', size)
                size = len(output)
            index = 0
            _continue = False
            single_stepped = False
            valid = True
            while index < len(output):
                if valid:  # Only print prompt and previous window if a valid key was pressed after prompt
                    end_index = min(index + size, len(output))  # Default set whole window
                    if single_stepped:
                        end_index = index + 1
                        single_stepped = False

                    # If C was pressed, update end of lines to dump rest of list
                    if _continue is True:
                        end_index = len(output)

                    for line in output[index:end_index]:
                        buffer_remaining = min(0, shutil.get_terminal_size().columns - len(line))  # Check number of character left in row
                        # clear out prevoius prompt
                        original_print(line, ' '*buffer_remaining)
                    if end_index == len(output):
                        break

                    # User control
                    original_print("--More-- (Space for next page, Enter for next line, 'c' for all lines, 'q' to quit)", end='')
                    original_print('\r', end='')
                response = getch()
                valid = False
                # Debug print for getch
                # print('response', ":".join("{:02x}".format(ord(c)) for c in response))
                if response == 'q':
                    valid = True
                    break
                elif response == 'c':
                    valid = True
                    _continue = True
                elif response == ' ':
                    valid = True
                    index = end_index
                elif response == '\n' or response == '\r':  # Handle macos, windows
                    valid = True
                    index = end_index
                    single_stepped = True


        # Paginate the captured output
        paginate_output(output_buffer, page_size)