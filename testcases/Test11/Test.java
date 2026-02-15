public class Test {

    public static void main(String[] args) {
        int[] a = new int[10];   // 1
        int x = a[0];            // 2
        int y = a[1];            // 3  (redundant — same abstract field [])
    }
}
