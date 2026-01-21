package ch.ethz.infsec.monitor;

import java.io.Serializable;
import java.util.List;

public interface Signature extends Serializable {
    List<String> getEvents();
    int getArity(String e);
    List<DataType> getTypes(String e);
    String getString();
}
