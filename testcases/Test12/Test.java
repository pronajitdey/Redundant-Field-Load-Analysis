public class Test {

    public static void main(String[] args) {
        int[] a = new int[10];   // 1
        int x = a[0];            // 2
        a[1] = 5;                // 3
        int y = a[0];            // 4  (not redundant)
    }
}
