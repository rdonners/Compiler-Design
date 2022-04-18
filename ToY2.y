
#include <fstream>
#include <memory>
#include <unordered_map>
#include <functional>
#include <numeric>
#include <set>



bool expression::is_compiletime_expr() const
{
    for(const auto& e: params) if(!e.is_compiletime_expr()) return false;
    switch(type)
    {
        case ex_type::number: case ex_type::string:
        case ex_type::add:    case ex_type::neg:    case ex_type::cand:  case ex_type::cor:
        case ex_type::comma:  case ex_type::nop:
            return true;
        case ex_type::ident:
            return is_function(ident);
        default:
            return false;
    }
}



// callv: Invokes the functor with args.
// Returns its return value, except, if func returns void, callv() returns def instead.
template<typename F, typename B, typename... A>
static decltype(auto) callv(F&& func, B&& def, A&&... args)
{
    if constexpr(std::is_invocable_r_v<B,F,A...>) { return std::forward<F>(func)(std::forward<A>(args)...); }
    else                                          { static_assert(std::is_void_v<std::invoke_result_t<F,A...>>);
                                                    std::forward<F>(func)(std::forward<A>(args)...); return std::forward<B>(def); }
}

std::string stringify(const expression& e, bool stmt);
std::string stringify_op(const expression& e, const char* sep, const char* delim, bool stmt = false, unsigned first=0, unsigned limit=~0u)
{
    std::string result(1, delim[0]);
    const char* fsep = "";
    for(const auto& p: e.params) { if(first) { --first; continue; }
                                   if(!limit--) break;
                                   result += fsep; fsep = sep; result += stringify(p, stmt); }
    if(stmt) result += sep;
    result += delim[1];
    return result;
}
std::string stringify(const expression& e, bool stmt = false)
{
    auto expect1 = [&]{ return e.params.empty() ? "?" : e.params.size()==1 ? stringify(e.params.front()) : stringify_op(e, "??", "()"); };
    switch(e.type)
    {
        // atoms
        case ex_type::nop    : return "";
        case ex_type::string : return "\"" + e.strvalue + "\"";
        case ex_type::number : return std::to_string(e.numvalue);
        case ex_type::ident  : return "?FPVS"[(int)e.ident.type] + std::to_string(e.ident.index) + "\"" + e.ident.name + "\"";
        // binary & misc
        case ex_type::add    : return stringify_op(e, " + ",  "()");
        case ex_type::eq     : return stringify_op(e, " == ", "()");
        case ex_type::cand   : return stringify_op(e, " && ", "()");
        case ex_type::cor    : return stringify_op(e, " || ", "()");
        case ex_type::comma  : return stmt ? stringify_op(e, "; ", "{}", true) : stringify_op(e, ", ",  "()");
        // unary
        case ex_type::neg    : return "-(" + expect1() + ")";
        case ex_type::deref  : return "*(" + expect1() + ")";
        case ex_type::addrof : return "&(" + expect1() + ")";
        // special
        case ex_type::copy   : return "(" + stringify(e.params.back()) + " = " + stringify(e.params.front()) + ")";
        case ex_type::fcall  : return "(" + (e.params.empty() ? "?" : stringify(e.params.front()))+")"+stringify_op(e,", ","()",false,1);
        case ex_type::loop   : return "while " + stringify(e.params.front()) + " " + stringify_op(e, "; ", "{}", true, 1);
        case ex_type::ret    : return "return " + expect1();
    }
    return "?";
}
static std::string stringify(const function& f)
{
    return stringify(f.code, true);
}

#include "textbox.hh"

static std::string stringify_tree(const function& f)
{
    textbox result;
    result.putbox(2,0, create_tree_graph(f.code, 132-2,
        [](const expression& e)
        {
            std::string p = stringify(e), k = p;
            switch(e.type)
            {
                #define o(n) case ex_type::n: k.assign(#n,sizeof(#n)-1); break;
                ENUM_EXPRESSIONS(o)
                #undef o
            }
            return e.params.empty() ? (k + ' ' + p) : std::move(k);
        },
        [](const expression& e) { return std::make_pair(e.params.cbegin(), e.params.cend()); },
        [](const expression& e) { return e.params.size() >= 1; }, // whether simplified horizontal layout can be used
        [](const expression&  ) { return true; },                 // whether extremely simplified horiz layout can be used
        [](const expression& e) { return is_loop(e); }));
    return "function " + f.name + ":\n" + stringify(f) + '\n' + result.to_string();
}

static bool equal(const expression& a, const expression& b)
{
    return (a.type == b.type)
        && (!is_ident(a) || (a.ident.type == b.ident.type && a.ident.index == b.ident.index))
        && (!is_string(a) || a.strvalue == b.strvalue)
        && (!is_number(a) || a.numvalue == b.numvalue)
        && std::equal(a.params.begin(), a.params.end(), b.params.begin(), b.params.end(), equal);
}



 using parameter_source = std::pair<std::string, std::size_t>; // Function name & parameter index
    using undefined_source = std::nullptr_t;                      // Dummy lessthan-comparable type
    using source_type      = std::variant<undefined_source, statement*, parameter_source>;

    static statement* is_statement(const source_type& s) { auto r = std::get_if<statement*>(&s); return r ? *r : nullptr; }
    static void is_statement(const statement*) = delete;

    struct AccessInfo
    {
        /* Info about registers, for each statement: */
        using StateType = std::vector<std::set<source_type>>;
        struct info
        {
            // For each parameter;
            //   if write param, list statements that directly depend on this write
            //   if read  param, list statements that can be possible sources of this value
            StateType params;
            // For all registers, indexed by register number
            StateType presence;
        };
        std::map<statement*, info> data;
    private:
        void Trace(statement* where, StateType&& state, bool follow_copies, bool include_ifnz_as_writer)
        {
            // Add all information from state into the data
            auto& mydata = data[where];

            // For this statement, add information about where
            // the values in each register come from at this point
            std::size_t changes{};
            for(std::size_t r=0; r<state.size(); ++r)
                for(const auto& s: state[r])
                    changes += mydata.presence[r].insert(s).second;

            if(follow_copies && is_copy(*where))
            {
                if(!changes) return;

                // After this insn, sources of tgt_reg are the same as sources of src_reg
                if(where->rhs() < statement::no_mask)
                    state[where->lhs()] = state[where->rhs()];
                else
                    state[where->lhs()] = {undefined_source()};
            }
            else
            {
                where->ForAllReadRegs([&](auto regno, auto index)
                {
                    changes += std::count_if(state[regno].begin(), state[regno].end(), [&](const auto& source)
                    {
                        auto writer = is_statement(source);
                        // Add writer info for the reader
                        return mydata.params[index].insert(source).second
                        // Add reader info for the writer, if it's a statement (and e.g. not a parameter)
                        + (writer && writer->ForAllWriteRegs([&](auto wregno, auto windex)
                            { return wregno == regno && data[writer].params[windex].insert(where).second; }));
                    });
                });
                if(!changes) return;

                // After this stmt, where is the only source for any register that it wrote into.
                where->ForAllWriteRegs([&](auto wregno, auto) { if(wregno < statement::no_mask) state[wregno] = { where }; });

                // If the statement is IFNZ and include_ifnz_as_writer is set,
                // we save the test knowledge as well.
                // The lhs of the IFNZ is a read-register, but based on the branch taken,
                // we can infer whether its value was zero or nonzero, and for the purposes
                // of some optimizations, this inference counts as a source of a value.
                if(include_ifnz_as_writer && is_ifnz(*where)) { if(where->lhs() < statement::no_mask) state[where->lhs()] = { where }; };
            }

            if(is_ifnz(*where) && where->cond) // pass copies of the arrays into cond processing
                Trace(where->cond, where->next ? StateType(state) : std::move(state), follow_copies, include_ifnz_as_writer);

            if(where->next) // Move the arrays into the tail processing.
                Trace(where->next, std::move(state), follow_copies, include_ifnz_as_writer);
        }
    public:
        // For every reachable insn, build a map where the value might be set for that register
        //   If follow_copies = true, tracks sources of values in register across COPY statements.
        //   If include_ifnz_as_writer = true, IFNZ statements are treated as write instructions.
        AccessInfo(const compilation& c, bool follow_copies, bool include_ifnz_as_writer)
        {
            // Calculate the list of register numbers to track
            std::size_t max_register_number = 0;
            for(const auto& s: c.all_statements)
                s->ForAllRegs([&](auto r, auto) {
                   max_register_number = std::max(max_register_number, std::size_t(r)+1); });
            for(const auto& f: c.function_parameters)
                max_register_number = std::max(max_register_number, f.second);

            // Initialize structure for all statements, including potentially unreachable ones
            for(const auto& s: c.all_statements)
                data.emplace(s.get(), info{ StateType(s->params.size()), StateType(max_register_number)});

            // Begin from all entry points
            for(const auto& [name,st]: c.entry_points)
            {
                // Initialize state for all known register numbers
                StateType state(max_register_number);

                std::size_t num_params = 0;
                if(auto i = c.function_parameters.find(name); i != c.function_parameters.end())
                    num_params = i->second;

                // At the function entry, all registers are undefined,
                // except those containing function parameters.
                for(statement::reg_type r = 0; r < max_register_number; ++r)
                    if(r < num_params)
                        state[r].insert(parameter_source{name, r});
                    else
                        state[r].insert(undefined_source{});

                // Trace recursively from this starting point.
                Trace(st, std::move(state), follow_copies, include_ifnz_as_writer);
            }
        }
    };


//
int main(int /*argc*/, char** argv)
{
    std::string filename = argv[1];
    std::ifstream f(filename);
    std::string buffer(std::istreambuf_iterator<char>(f), {});

    lexercontext lexercontext;
    lexercontext.cursor = buffer.c_str();
    lexercontext.loc.begin.filename = &filename;
    lexercontext.loc.end.filename   = &filename;

    yy::conj_parser parser(lexercontext);
    parser.parse();
    func_list = std::move(lexercontext.func_list);

    std::cerr << "Initial\n";
    for(const auto& f: func_list) std::cerr << stringify_tree(f);

    std::cerr << "Final\n";
    for(const auto& f: func_list) std::cerr << stringify_tree(f);

    compilation code;
    code.Compile();

    std::cerr << "COMPILED CODE\n";
    code.Dump(std::cerr);

    code.Optimize();

    std::cerr << "OPTIMIZED CODE\n";
    code.Dump(std::cerr);
}