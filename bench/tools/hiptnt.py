import benchexec.util as util
import benchexec.tools.template
import benchexec.result as result

class Tool(benchexec.tools.template.BaseTool):
    """
    Wrapper for HipTNT+
    """

    def executable(self):
        return util.find_executable("hiptnt_sv")

    def name(self):
        return "HipTNT+"

    def determine_result(self, returncode, returnsignal, output, isTimeout):
        output = "\n".join(output)
        if ((returnsignal == 9) or (returnsignal == 15)) and isTimeout:
            status = "TIMEOUT"
        elif returnsignal == 9:
            status = "KILLED BY SIGNAL 9"
        elif "TRUE" in output:
            status = result.RESULT_TRUE_PROP
        elif "FALSE" in output:
            status = result.RESULT_FALSE_PROP
        elif returncode != 0:
            status = "ERROR ({0})".format(returncode)
        else:
            status = result.RESULT_UNKNOWN
        return status
