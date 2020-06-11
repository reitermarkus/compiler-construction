void foo(string s) {
    s = "foo";
    print(s);
}

int main() {
    string s;
    s = "bar";
    foo(s);
    print_nl();
    print(s); /* outputs bar */
    return 0;
}
