import java.util.TreeSet;
import java.util.*;

import soot.*;
import soot.options.Options;

public class PA2 {
    public static void main(String[] args) {
        String classPath = "./testcases/" + args[0];

        // Set up arguments for Soot
        String[] sootArgs = {
            "-cp", classPath,
            "-pp", // sets the class path for Soot
            "-f", "J",
            "-t", "1",
            "-main-class", "Test", // specify the main class
            "-process-dir", classPath
        };

        // Create transformer for analysis
        AnalysisTransformer analysisTransformer = new AnalysisTransformer();

        // Add transformer to appropriate pack in PackManager; PackManager will run all packs when soot.Main.main is called
        PackManager.v().getPack("jtp").add(new Transform("jtp.dfa", analysisTransformer));

        // Set Soot options (Used to maintain line numbers from source code)
        Options.v().set_keep_line_number(true);

        // Call Soot's main method with arguments
        soot.Main.main(sootArgs);

        // Print redundant information
        for (String className : RedundancyRepository.data.keySet()) {
            Map<String, TreeSet<RedundantInfo>> methodMap = RedundancyRepository.data.get(className);

            for (String methodName : methodMap.keySet()) {
                TreeSet<RedundantInfo> set = methodMap.get(methodName);

                if (!set.isEmpty()) {
                    System.out.println(className + ":" + methodName);

                    for (RedundantInfo r : set) {
                        System.out.println(r.line + ":" + r.stmt);
                    }
                }
            }
        }
    }
}
