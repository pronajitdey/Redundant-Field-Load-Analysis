public class Test {
    int f;

    public static void main(String[] args) {
        Test o = new Test();    // 1
        int x = o.f;        // 2
        o.f = 10;           // 3
        int y = o.f;        // 4  (not redundant)
    }
}
