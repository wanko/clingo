#include "tests.hh"
#include <iostream>
#include <fstream>

namespace Clingo { namespace Test {

using V = Variant<int, std::string, std::unique_ptr<int>>;

struct D {
    D(std::string &r) : r(r) { r = "not called"; }
    void visit(int &x) {
        r = std::to_string(x);
    }
    void visit(std::string &x) {
        r = x;
    }
    void visit(std::unique_ptr<int> &x) {
        r = std::to_string(*x);
    }
    std::string &r;
};

TEST_CASE("visitor", "[clingo]") {
    V x{10};
    REQUIRE(x.is<int>());
    REQUIRE(!x.is<std::string>());
    REQUIRE(x.get<int>() == 10);
    std::string s = "s1";
    x = static_cast<std::string const &>(s);
    REQUIRE(x.get<std::string>() == "s1");
    x = s;
    REQUIRE(x.get<std::string>() == "s1");
    x = std::move(s);
    REQUIRE(x.get<std::string>() == "s1");
    s = "s2";
    REQUIRE(V{s}.get<std::string>() == "s2");
    REQUIRE(V{static_cast<std::string const &>(s)}.get<std::string>() == "s2");
    REQUIRE(V{std::move(s)}.get<std::string>() == "s2");

    V y = x;
    REQUIRE(y.get<std::string>() == "s1");
    x = y;
    REQUIRE(x.get<std::string>() == "s1");

    std::string r;
    y.accept(D(r));
    REQUIRE(r == "s1");
    x.accept(D(r));
    REQUIRE(r == "s1");

    x = V::make<std::unique_ptr<int>>(nullptr);
    REQUIRE(!x.get<std::unique_ptr<int>>());

    x.swap(y);
    REQUIRE(!y.get<std::unique_ptr<int>>());
    REQUIRE(x.get<std::string>() == "s1");
};

} } // namespace Test Clingo