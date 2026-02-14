import java.util.*;

public class RedundancyRepository {

    // class -> method -> list of (line, statement)
    public static Map<String,
        Map<String, TreeSet<RedundantInfo>>> data = new TreeMap<>();    

    public static void add(
        String className,
        String methodName,
        int line,
        String stmt
    ) {
        data.computeIfAbsent(className,
            k -> new TreeMap<>()
        ).computeIfAbsent(methodName,
            k -> new TreeSet<>()
        ).add(new RedundantInfo(line, stmt));
    }
}

class RedundantInfo implements Comparable<RedundantInfo> {
    int line;
    String stmt;

    public RedundantInfo(int line, String stmt) {
        this.line = line;
        this.stmt = stmt;
    }

    @Override
    public int compareTo(RedundantInfo other) {
        return Integer.compare(this.line, other.line);
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof RedundantInfo)) return false;

        RedundantInfo r = (RedundantInfo) o;
        return this.line == r.line && this.stmt.equals(r.stmt);
    }

    @Override
    public int hashCode() {
        return 31 * line + stmt.hashCode();
    }
}
