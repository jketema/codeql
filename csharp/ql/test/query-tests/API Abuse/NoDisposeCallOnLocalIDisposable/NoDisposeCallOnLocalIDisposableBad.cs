using System;
using System.IO;

class Bad
{
    long GetLength(string file)
    {
        var stream = new FileStream(file, FileMode.Open); // $ Alert
        return stream.Length;
    }
}
