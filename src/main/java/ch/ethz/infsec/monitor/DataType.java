package ch.ethz.infsec.monitor;

public enum DataType {
    INTEGRAL("int"),
    FLOAT("float"),
    STRING("string");

    private final String name;

    DataType(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }

    public Object parse(String s) {
        switch (this) {
            case INTEGRAL:
                return Long.parseLong(s);
            case FLOAT:
                return Double.parseDouble(s);
            case STRING:
                return s;
        }
        return null;
    }
}
