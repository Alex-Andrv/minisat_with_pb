//
// Created by Alexander Andreev on 08.03.2023.
//

#include <exception>

namespace Minisat {

    class bad_optional_access : public std::exception {
    public:
        bad_optional_access() : message_("bad optional access") {}

        virtual const char *what() const noexcept {
            return message_;
        }

    private:
        const char* message_;
    };

    template<typename T>
    struct optional {
    private:
        bool _has_value;
        T _value;
    public:
        optional() : _has_value{false}, _value{} {}

        optional(T v) : _has_value{true}, _value{v} {}

        bool has_value() const { return _has_value; }

        T value() const {
            if (_has_value) return _value;
            throw bad_optional_access();
        }

        T value_or(T def) const {
            return _has_value ? _value : def;
        }

        optional<T> &operator=(T v) {
            _has_value = true;
            _value = v;
            return *this;
        }

        void reset() { _has_value = false; }
    };
}