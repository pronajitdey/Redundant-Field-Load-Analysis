public class Test {
    Test f;

    public void test(int x) {
        Test o = new Test();    // 1
        o.f = new Test();        // 2
        Test a = o.f;

        boolean c = true;
        if (x > 10) {
            Test y = o.f;    // 3  (redundant)
        } else {
            Test z = o.f;    // 4  (redundant)
        }
    }

    public static void main(String[] args) {
        Test x = new Test(); // O17
        x.test(10);
    }
}
