public class Test {
    Test f;

    public void test(int x) {
        Test o = new Test();    // 1
        o.f = new Test();        // 2
        Test a = o.f;

        boolean c = true;
        if (x > 10) {
            o.f = new Test();   
        }

        Test y = o.f; // not redundant
    }

    public static void main(String[] args) {
        Test x = new Test(); 
        x.test(10);
    }
}
