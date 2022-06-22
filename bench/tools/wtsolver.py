import benchexec.util as util
import benchexec.tools.smtlib2


class Tool(benchexec.tools.smtlib2.Smtlib2Tool):
    """
    Tool info for weak theory.
    """

    def executable(self):
        return util.find_executable("bigtop.exe")

    def version(self, executable):
        return '1.0'

    def name(self):
        return "WTQFNRASolver"

    def cmdline(self, executable, options, tasks, propertyfile=None, rlimits={}):
        assert len(tasks) <= 1, "only one inputfile supported"
        return [executable] + options + tasks