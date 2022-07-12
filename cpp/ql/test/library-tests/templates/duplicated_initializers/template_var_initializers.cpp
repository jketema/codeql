template <class _Ty1, class _Ty2> bool is_same_v = false;
template <class _Ty> bool is_same_v<_Ty, _Ty> = true;

bool b1 = is_same_v<int, int>;
bool b2 = is_same_v<long, long>;
bool b3 = is_same_v<long, int>;

// semmle-extractor-options: --edg --c++20
