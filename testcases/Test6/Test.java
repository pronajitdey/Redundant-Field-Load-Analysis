public class Test {
    int f;

    public static void main(String[] args) {
        Test a = new Test();    // 1
        Test b = a;           // 2
        int x = a.f;        // 3
        int y = b.f;        // 4  (redundant)
    }
}
