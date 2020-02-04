# Author: Bohua Zhan

import contextlib
import copy


class Settings:
    """Global settings."""
    def __init__(self):
        # Whether to print unicode.
        self.unicode = False

        # Whether to print with highlight.
        self.highlight = False

        # Line length
        self.line_length = None

    def __copy__(self):
        res = Settings()
        res.__dict__.update(self.__dict__)
        return res

settings = Settings()

@contextlib.contextmanager
def global_setting(**kwargs):
    """Set global settings in a with statement."""
    # Record previous settings
    global settings
    old_settings = copy.copy(settings)

    # Update settings
    settings.__dict__.update(kwargs)
    try:
        yield None
    finally:
        # Recover previous settings
        settings.__dict__.update(old_settings.__dict__)
