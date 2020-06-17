import benchexec.util as util
import benchexec.tools.template
import benchexec.result as result

class Tool(benchexec.tools.template.BaseTool):
    """
    Wrapper for ComPACT tool
    """

    def executable(self):
        return util.find_executable("duet.exe")

    def name(self):
        return "ComPACT"

    def determine_result(self, returncode, returnsignal, output, isTimeout):
        output = "\n".join(output)
        if ((returnsignal == 9) or (returnsignal == 15)) and isTimeout:
            status = "TIMEOUT"
        elif returnsignal == 9:
            status = "KILLED BY SIGNAL 9"
        elif "Program always terminates" in output:
            status = result.RESULT_TRUE_PROP
        elif returncode != 0:
            status = "ERROR ({0})".format(returncode)
        else:
            status = result.RESULT_UNKNOWN
        return status
