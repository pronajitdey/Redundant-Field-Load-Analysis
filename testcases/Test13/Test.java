public class Test {
    int f;

    void foo(Test p) {
        p.f = 5;
    }

    public static void main(String[] args) {
        Test o = new Test();   // 1
        int x = o.f;         // 2
        o.f = 10;
        o.foo(o);            // 3
        int y = o.f;         // 4  (not redundant if conservative)
    }
}
