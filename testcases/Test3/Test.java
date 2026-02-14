public class Test {
    Test f;
    public void test(int x) {
        Test b = new Test(); // O4
        Test a;
        if (x > 12) {
            a = new Test(); // O7
        } else {
            a = new Test(); // O9
        }
        a.f = b;
    }

    public static void main(String[] args) {
        Test x = new Test(); // O15
        x.test(10);
    }
}