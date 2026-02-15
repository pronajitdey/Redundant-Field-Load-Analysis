public class Test {
    int f;

    public static void main(String[] args) {
        Test o = new Test();    // 1
        int x = o.f;        // 2

        int i = 0;
        while (i < 2) {
            int y = o.f;    // 3  (redundant)
            i++;
        }
    }
}
