public class Test {
    int f;
    int g;

    void foo(Test p) {
        p.g = 5;
    }

    public static void main(String[] args) {
        Test o = new Test();   // 1
        int x = o.f;         // 2
        o.foo(o);            // 3
        int y = o.f;         // 4  (redundant if selective kill)
    }
}
