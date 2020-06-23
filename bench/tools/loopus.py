import benchexec.util as util
import benchexec.tools.template
import benchexec.result as result

class Tool(benchexec.tools.template.BaseTool):
    """
    Wrapper for Loopus
    """

    def executable(self):
        return util.find_executable("loopus-c")

    def name(self):
        return "loopus"

    def determine_result(self, returncode, returnsignal, output, isTimeout):
        output = "\n".join(output)
        if ((returnsignal == 9) or (returnsignal == 15)) and isTimeout:
            status = "TIMEOUT"
        elif returnsignal == 9:
            status = "KILLED BY SIGNAL 9"
        elif "FAILED" in output:
            status = result.RESULT_UNKNOWN
        elif returncode != 0:
            status = "ERROR ({0})".format(returncode)
        else:
            status = result.RESULT_TRUE_PROP
        return status
