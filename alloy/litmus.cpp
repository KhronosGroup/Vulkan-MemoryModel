// Copyright (c) 2017-2018 Khronos Group. This work is licensed under a
// Creative Commons Attribution 4.0 International License; see
// http://creativecommons.org/licenses/by/4.0/

// Vulkan Memory Model
// Convert an assembly-like syntax to the Alloy model.
//
// Name from first command line argument, input path in second argument,
// output to files in directory specified by third argument

// Input format:
//
// Comments: "//" must be the first two characters on a comment line.
//
// "NEWQF"/"NEWWG"/"NEWSG"/"NEWTHREAD" switch to a new queue family/workgroup/subgroup/thread.
// No way to switch back to previous thread/group.
// NEWTHREAD takes an optional thread number, which can
// be used with SSW. If a thread number is not present, the initial thread is
// assigned number zero and other threads are assigned a thread number one
// greater than the previous thread. Within a thread, instructions are listed
// in program order.
//
// An instruction is of the form:
//
//    token[.token]^N [variable [= value [value2]]] [cbarinstancenumber]
//
// That is, the opcode consists of an arbitrary number of '.'-separated tokens.
// Load/store/atomic operations take a variable name (any string), which is
// used to determine which instructions access the same memory locations. Those
// operations also optionally take "= value" where value is an integer.
// Matching store/load values are used to form reads-from edges. A load with
// "= 0" reads-from the initial value. Loads and/or stores without a value
// assignment are less constrained.
//
// Atomic RMWs can be expressed as either "ld.st.atom" (or any permutation of
// that), or simply as "rmw". They accept the additional "value2" (write
// value), and treat "value" as the read value.
//
// "cbar" instructions don't take a variable, and instead take an "instance
// number" which is an integer value used to match control barrier instructions
// from the same dynamic instance as specified in multiple threads.
//
// Valid tokens are:
//
// "st" - store/write
// "ld" - load/read
// "membar" - OpMemoryBarrier ("fence")
// "atom" - atomic. Used with st and/or ld to indicate the type of atomic
// "rmw" - read and write and atomic (alias for setting these separately)
// "acq" - acquire semantics
// "rel" - release semantics (can use both acq and rel with membar/cbar)
// "sc0" - storage class 0
// "sc1" - storage class 1
// "semsc0" - storage class 0 in semantics
// "semsc1" - storage class 1 in semantics
// "scopesg" - Subgroup scope (for atomics/barriers)
// "scopewg" - Workgroup scope (for atomics/barriers)
// "scopeqf" - QueueFamily scope (for atomics/barriers)
// "scopedev" - Device scope (for atomics/barriers)
// "cbar" - OpControlBarrier
// "avdevice" - device domain availability operation
// "visdevice" - device domain visibility operation
// "semav" - availability operation specified in memory semantics
// "semvis" - visibility operation specified in memory semantics
// "av" - per-instruction availability operation
// "vis" - per-instruction visibility operation
// "nonpriv" - obeys inter-thread ordering (default for av/vis, must be set for noncoherent)
//
// There is limited validation of the input. See InstructionState::warn.
// For example, it checks some basic rules like "all atomics and barriers
// must specify a scope" which, if violated, makes an execution trivially
// unsatisfiable.
//
// "SLOC", "SSW", "SATISFIABLE", "NOSOLUTION", and "NOCHAINS" are non-instruction
// directives.
//
// "SLOC" takes two variable name strings and specifies that they access
// the same memory location (but are different references). Each variable
// name is always a unique reference. By default, each variable name is
// also a unique location. SLOC allows declaring that two distinct variable
// names (references) share the same location.
//
// "SSW" takes two integer operands which are thread numbers, and specifies
// that the first thread system-synchronizes-with the second thread.
//
// "SATISFIABLE", and "NOSOLUTION" begin specification of a unit test, and
// indicates whether alloy should find a solution. The remainder of the
// line is code pasted directly into the predicate, along
// with the program info. For example, a common test is:
//
// SATISFIABLE consistent[X] && #dr=0
//
// indicating that the program can be satisfied by a consistent execution
// with no data races. Each line is an independent test.
//
// "NOCHAINS" can be put after SATISFIABLE or NOSOLUTION to indicate that
// the test should run assuming the implementation does not support
// availability and visibility chains with more than one element.
//
#include <algorithm>
#include <sstream>
#include <iostream>
#include <fstream>
#include <vector>
#include <set>
#include <map>
#include <cstdio>
#include <cstring>
#include <cassert>

using namespace std;

// Track what variable/value is used for a load or store. Used to
// determine read-from edges. Also used to track control barrier
// instances.
class LoadStore {
public:
    LoadStore() : var(), value(-1), value2(-1), cbarInstance(-1) {}
    string var;
    int value;
    int value2;
    int cbarInstance;
};

// Track what instruction fields are set for each instruction.
class InstructionState {
public:

    InstructionState() : loadStore(100), threads(100) {}

    set<int> W, R, F, A, ACQ, REL, SC0, SC1, SEMSC0, SEMSC1, SCOPESG, SCOPEWG, SCOPEQF, SCOPEDEV, CBAR, AVDEVICE, VISDEVICE, SEMAV, SEMVIS, AV, VIS, NONPRIV;

    vector<LoadStore> loadStore;

    // Track the set of instructions in each thread
    vector<set<int> > threads;

    bool isRead(int instnum) const { return R.find(instnum) != R.end(); }
    bool isWrite(int instnum) const { return W.find(instnum) != W.end(); }
    int getReadValue(int instnum) const
    {
        if (!isRead(instnum)) {
            printf("WARNING: calling getReadValue on a non-read");
        }
        return loadStore[instnum].value;
    }
    int getWriteValue(int instnum) const
    {
        if (!isWrite(instnum)) {
            printf("WARNING: calling getWriteValue on a non-write");
        }
        return (isRead(instnum) && isWrite(instnum)) ? loadStore[instnum].value2 : loadStore[instnum].value;
    }

    void processToken(const string &token, int instnum)
    {
#define CASE(X, Y) if (token == Y) { X.insert(instnum); }
        CASE(W, "st")
        CASE(R, "ld")
        CASE(F, "membar")
        CASE(A, "atom")
        CASE(ACQ, "acq")
        CASE(REL, "rel")
        CASE(SC0, "sc0")
        CASE(SC1, "sc1")
        CASE(SEMSC0, "semsc0")
        CASE(SEMSC1, "semsc1")
        CASE(SCOPESG, "scopesg")
        CASE(SCOPEWG, "scopewg")
        CASE(SCOPEQF, "scopeqf")
        CASE(SCOPEDEV, "scopedev")
        CASE(CBAR, "cbar")
        // "rmw" is an alias for R, W, and A
        CASE(R, "rmw")
        CASE(W, "rmw")
        CASE(A, "rmw")
        CASE(AVDEVICE, "avdevice")
        CASE(VISDEVICE, "visdevice")
        CASE(SEMAV, "semav")
        CASE(SEMVIS, "semvis")
        CASE(AV, "av")
        CASE(VIS, "vis")
        CASE(NONPRIV, "nonpriv")
#undef CASE

        // CBARs are also treated as fences if they acq/rel
        if ((ACQ.find(instnum) != ACQ.end() || REL.find(instnum) != REL.end()) &&
            CBAR.find(instnum) != CBAR.end()) {
            F.insert(instnum);
        }
        // Atomics implicitly have AV/VIS ops
        if (A.find(instnum) != A.end()) {
            if (W.find(instnum) != W.end()) {
                AV.insert(instnum);
            }
            if (R.find(instnum) != R.end()) {
                VIS.insert(instnum);
            }
        }
        // AV, VIS, and atomics are all implicitly nonpriv
        if (AV.find(instnum) != AV.end() ||
            VIS.find(instnum) != VIS.end() ||
            A.find(instnum) != A.end()) {
            NONPRIV.insert(instnum);
        }
    }

    // print "X.name = E2+...+En" or "X.name = none"
    void printOne(stringstream &o, const set<int> &s, string name)
    {
        o << "    X." << name << " = ";
        set<int>::iterator it;
        if (s.begin() == s.end()) {
            o << "none";
        } else {
            for (it = s.begin(); it != s.end();) {
                o << "E" << *it;
                it++;
                if (it != s.end()) {
                    o << "+";
                }
            }
        }
        o << endl;
    }

    void print(stringstream &o)
    {
#define CASE(X) printOne(o, X, #X);
        CASE(W)
        CASE(R)
        CASE(F)
        CASE(A)
        CASE(ACQ)
        CASE(REL)
        CASE(SC0)
        CASE(SC1)
        CASE(SEMSC0)
        CASE(SEMSC1)
        CASE(SCOPESG)
        CASE(SCOPEWG)
        CASE(SCOPEQF)
        CASE(SCOPEDEV)
        CASE(CBAR)
        CASE(AVDEVICE)
        CASE(VISDEVICE)
        CASE(SEMAV)
        CASE(SEMVIS)
        CASE(AV)
        CASE(VIS)
        CASE(NONPRIV)
#undef CASE
    }

    void warn(int instnum)
    {
        if ((A.find(instnum) != A.end() ||
             F.find(instnum) != F.end() ||
             CBAR.find(instnum) != CBAR.end() ||
             AV.find(instnum) != AV.end() ||
             VIS.find(instnum) != VIS.end()) &&
            (SCOPESG.find(instnum) == SCOPESG.end() &&
             SCOPEWG.find(instnum) == SCOPEWG.end() &&
             SCOPEQF.find(instnum) == SCOPEQF.end() &&
             SCOPEDEV.find(instnum) == SCOPEDEV.end())) {
            fprintf(stderr, "WARNING: atomic or barrier or av/vis without scope\n");
        }
        if (R.find(instnum) != R.end() ||
            W.find(instnum) != W.end()) {
            if (SC0.find(instnum) == SC0.end() && SC1.find(instnum) == SC1.end()) {
                fprintf(stderr, "WARNING: read or write without storage class\n");
            }
            if (loadStore[instnum].var == "") {
                fprintf(stderr, "WARNING: read or write without variable\n");
            }
        }
        if (CBAR.find(instnum) != CBAR.end() &&
            loadStore[instnum].cbarInstance == -1) {
            fprintf(stderr, "WARNING: cbar without instance\n");
        }
        if (F.find(instnum) != F.end() &&
            (ACQ.find(instnum) == ACQ.end() && REL.find(instnum) == REL.end())) {
            fprintf(stderr, "WARNING: membar without acq or rel\n");
        }
        if (loadStore[instnum].value2 != -1 &&
            (A.find(instnum) == A.end() ||
             R.find(instnum) == R.end() ||
             W.find(instnum) == W.end())) {
            fprintf(stderr, "WARNING: second value requires RMW atomic\n");
        }
        if ((SEMSC0.find(instnum) != SEMSC0.end() || SEMSC1.find(instnum) != SEMSC1.end()) &&
            !(ACQ.find(instnum) != ACQ.end() || REL.find(instnum) != REL.end())) {
            fprintf(stderr, "WARNING: ACQ+REL = SEMSC0+SEMSC1\n");
        }
        if (SEMAV.find(instnum) != SEMAV.end() && REL.find(instnum) == REL.end()) {
            fprintf(stderr, "WARNING: SEMAV in REL\n");
        }
        if (SEMVIS.find(instnum) != SEMVIS.end() && ACQ.find(instnum) == ACQ.end()) {
            fprintf(stderr, "WARNING: SEMVIS in ACQ\n");
        }
    }
};

// If allB is false, print the sequence Ea->Ea+1->...Eb-1. If allB is true,
// print Ea->Eb, Ea+1->Eb, ... Eb-1->Eb
void sequenceInSuffix(stringstream &o, int a, int b, bool allB, string suffix)
{
    if (a == b) {
        return;
    }
    for (int i = a; i < b; ++i) {
        int j = allB ? b : (i+1);
        o << "(E" << i << "->E" << j << ")";
        if (i != b-1) {
            o << "+";
        }
    }
    
    o << suffix << "\n";
}

int main(int argc, char *argv[])
{
    string line;
    InstructionState instState;
    int instnum = -1;
    int firstInstInThread = 0;
    int firstInstInSG = 0;
    int firstInstInWG = 0;
    int firstInstInQF = 0;

    if (argc != 4) {
        printf("usage: litmus name inputdir outputdir\n");
        return 1;
    }

    ifstream in;
    in.open(string(argv[2])+"/"+argv[1]);

    stringstream o;

    int threadnum = 0;
    int numEvents = 0;

    vector<string> sswInputs;
    vector<string> slocInputs;
    vector<string> testInputs;

    while (getline(in, line)) {
        // skip comments
        if (line.length() < 2 || line.substr(0, 2) == "//") {
            continue;
        }

        while (line.back() == '\r' || line.back() == '\n') {
            line.pop_back();
        }

        if (line.find("SATISFIABLE") == 0 || line.find("NOSOLUTION") == 0) {
            testInputs.push_back(line);
            continue;
        }

        if (line.find("SSW") == 0) {
            sswInputs.push_back(line);
            continue;
        }

        if (line.find("SLOC") == 0) {
            slocInputs.push_back(line);
            continue;
        }

        // Close a queue family
        if (line.find("NEWQF") != string::npos) {
            if (instnum != -1) {
                o << "    "; sequenceInSuffix(o, firstInstInQF, instnum, false, " in X.sqf");
                o << "    no ("; sequenceInSuffix(o, 0, instnum+1, true, ") & X.sqf");
                firstInstInQF = instnum+1;
            }
            continue;
        }

        // Close a workgroup
        if (line.find("NEWWG") != string::npos) {
            if (instnum != -1) {
                o << "    "; sequenceInSuffix(o, firstInstInWG, instnum, false, " in X.swg");
                o << "    no ("; sequenceInSuffix(o, 0, instnum+1, true, ") & X.swg");
                firstInstInWG = instnum+1;
            }
            continue;
        }

        // Close a subgroup
        if (line.find("NEWSG") != string::npos) {
            if (instnum != -1) {
                o << "    "; sequenceInSuffix(o, firstInstInSG, instnum, false, " in X.ssg");
                o << "    no ("; sequenceInSuffix(o, 0, instnum+1, true, ") & X.ssg");
                firstInstInSG = instnum+1;
            }
            continue;
        }

        // Close a thread
        if (line.find("NEWTHREAD") != string::npos) {
            if (instnum != -1) {
                o << "    "; sequenceInSuffix(o, firstInstInThread, instnum, false, " in X.immpo");
                o << "    no ("; sequenceInSuffix(o, 0, instnum+1, true, ") & X.immpo");
                firstInstInThread = instnum+1;
            }
            // look for a thread number, otherwise just increment to the next
            // thread number
            size_t nextpos = line.find_first_of("0123456789");
            if (nextpos != string::npos) {
                line = line.substr(nextpos);
                threadnum = atoi(line.c_str());
            } else {
                threadnum++;
            }
            assert(instState.threads[threadnum].empty());
            continue;
        }

        // parse an instruction
        instnum++;

        instState.threads[threadnum].insert(instnum);

        // Peel out the instruction (everything before the first space)
        // and look at each token (separated by '.')
        size_t firstspace = line.find(' ');
        string inst = line.substr(0, firstspace);

        while (true) {
            size_t nextpos = inst.find('.');
            string token = inst.substr(0, nextpos);

            instState.processToken(token, instnum);

            if (nextpos == string::npos) {
                break;
            }
            inst = inst.substr(nextpos+1);
        }

        // Look for a variable assignment (e.g. "x = 1") or
        // a control barrier dynamic instance number
        if (line.length() > firstspace) {
            if (instState.CBAR.find(instnum) != instState.CBAR.end()) {
                line = line.substr(firstspace);
                line = line.substr(line.find_first_not_of(" "));
                instState.loadStore[instnum].cbarInstance = atoi(line.c_str());
            } else {
                line = line.substr(firstspace);
                line = line.substr(line.find_first_not_of(" ="));
                string var = line.substr(0, line.find_first_of(" ="));

                instState.loadStore[instnum].var = var;

                line = line.substr(var.length());

                if (line.find('=') != string::npos) {
                    line = line.substr(line.find_first_not_of(" ="));

                    instState.loadStore[instnum].value = atoi(line.c_str());
                }
                // Look for whitespace and another value
                if (line.find(' ') != string::npos) {
                    line = line.substr(line.find(' '));

                    if (line.find_first_of("1234567890")) {
                        line = line.substr(line.find_first_not_of(" "));
                        instState.loadStore[instnum].value2 = atoi(line.c_str());
                    }
                }
            }
        }

        instState.warn(instnum);
    }

    numEvents = instnum+1;

    stringstream ssw;
    for (size_t i = 0; i < sswInputs.size(); ++i) {
        line = sswInputs[i];
        int threadA, threadB;
        line = line.substr(strlen("SSW"));
        line = line.substr(line.find_first_of("1234567890"));
        threadA = atoi(line.c_str());
        line = line.substr(line.find(" "));
        line = line.substr(line.find_first_of("1234567890"));
        threadB = atoi(line.c_str());

        if (ssw.str().length() != 0) {
            ssw << "+";
        }
        bool first = true;
        // SSW from each instruction of threadA to each instruction of threadB
        for (int i = *instState.threads[threadA].begin(); i <= *instState.threads[threadA].rbegin(); ++i) {
        for (int j = *instState.threads[threadB].begin(); j <= *instState.threads[threadB].rbegin(); ++j) {
            if (!first) {
                ssw << "+";
            }
            first = false;
            ssw << "E" << i << "->E" << j;
        }
        }
    }
    if (ssw.str().length() == 0) {
        o << "    no X.ssw\n";
    } else {
        o << "    X.ssw = " << ssw.str() << "\n";
    }

    // Close the last QF/WG/SG/thread
    o << "    "; sequenceInSuffix(o, firstInstInQF, instnum, false, " in X.sqf");
    o << "    "; sequenceInSuffix(o, firstInstInWG, instnum, false, " in X.swg");
    o << "    "; sequenceInSuffix(o, firstInstInSG, instnum, false, " in X.ssg");
    o << "    "; sequenceInSuffix(o, firstInstInThread, instnum, false, " in X.immpo");

    // no backwards/self edges (En->Em with n>=m) in immpo
    o << "    no *(";
    for (int i = 1; i <= instnum; ++i) {
        o << "(E" << i << "->E" << i-1 << ")";
        if (i != instnum) o << "+";
    }
    o << ") & X.immpo\n";


    // print simple state for all instructions
    instState.print(o);

    // Determine read-from and RFINIT from the variable load/stores
    for (int i = 0; i <= instnum; ++i) {
    for (int j = 0; j <= instnum; ++j) {
        if (instState.loadStore[j].var != "") {
            if (instState.loadStore[i].var == instState.loadStore[j].var &&
                instState.isWrite(i) && instState.isRead(j) &&
                instState.getWriteValue(i) == instState.getReadValue(j)) {
                o << "    (E" << i << "->E" << j << ") in X.rf\n";
            } else if (i == j && instState.isRead(j) && instState.getReadValue(j) == 0) {
                o << "    E" << j << " in X.RFINIT\n";
            }
        }
    }
    }

    // Find each new variable and put all uses of it in X.pgmsref
    set<string> variables;
    bool firstSref = true;
    for (int j = 0; j <= instnum; ++j) {
        string v = instState.loadStore[j].var;
        if (v != "" && variables.find(v) == variables.end()) {
            variables.insert(v);
            for (int i = j+1; i <= instnum; ++i) {
                if (instState.loadStore[i].var == v) {
                    if (firstSref) {
                        o << "    X.pgmsref = ";
                    } else {
                        o << "+";
                    }
                    firstSref = false;
                    o << "(E" << i << "->E" << j << ")";
                }
            }
        }
    }
    if (firstSref) {
        o << "    no X.pgmsref";
    }
    o << "\n";
    o << "    X.pgmsloc = X.pgmsref";

    stringstream sloc;
    for (size_t i = 0; i < slocInputs.size(); ++i) {
        line = slocInputs[i];

        string locA, locB;
        line = line.substr(strlen("SLOC"));
        line = line.substr(line.find_first_not_of(" "));
        locA = line.substr(0, line.find(" "));
        line = line.substr(line.find(" "));
        line = line.substr(line.find_first_not_of(" "));
        locB = line.substr(0, line.find(" "));

        for (int i = 0; i <= instnum; ++i) {
        for (int j = 0; j <= instnum; ++j) {
            if (instState.loadStore[i].var == locA &&
                instState.loadStore[j].var == locB) {
                o << "+(E" << i << "->E" << j << ")";
            }
        }
        }
    }
    o << "\n";

    // print groups of related control barrier instances
    set<int> cbarInsts;
    for (int j = 0; j <= instnum; ++j) {
        int v = instState.loadStore[j].cbarInstance;
        if (v != -1 && cbarInsts.find(v) == cbarInsts.end()) {
            cbarInsts.insert(v);
            o << "    ";
            bool first = true;
            for (int i = j+1; i <= instnum; ++i) {
                if (instState.loadStore[i].cbarInstance == v) {
                    if (!first) {
                        o << "+";
                    }
                    first = false;
                    o << "(E" << i << "->E" << j << ")";
                }
            }
            o << " in X.scbarinst\n";

            if (j != 0) {
                o << "    no ("; sequenceInSuffix(o, 0, j, true, ") & X.scbarinst");
            }
        }
    }

    ofstream outals, outreference;
    // outputdir/filename.gen
    outals.open(string(argv[3])+"/"+argv[1]+".gen");
    // outputdir/filename.ref
    outreference.open(string(argv[3])+"/"+argv[1]+".ref");

    outals << "open spirv\n";
    int testnum = 0;
    for (size_t i = 0; i < testInputs.size(); ++i) {
        line = testInputs[i];

        if (line.find("SATISFIABLE") != 0 && line.find("NOSOLUTION") != 0) {
            printf("error in tests\n");
            return 1;
        }
        if (line.find("SATISFIABLE") == 0) {
            line = line.substr(strlen("SATISFIABLE"));
            outreference << "SATISFIABLE\n";
        } else {
            line = line.substr(strlen("NOSOLUTION"));
            outreference << "NOSOLUTION\n";
        }

        bool noChains = false;
        if (line.find("NOCHAINS") != string::npos) {
            noChains = true;
            line = line.substr(line.find("NOCHAINS") + strlen("NOCHAINS"));
        }

        outals << "pred gentest" << testnum << "[X:Exec] {\n";
        outals << "  #Exec = 1\n";
        outals << "  #E = " << numEvents << "\n";
        outals << "  some disj ";
    
        for (int i = 0; i < numEvents; ++i) {
            outals << "E" << i;
            if (i != numEvents-1) {
                outals << ",";
            }
        }
        outals << " : E {\n";
        outals << o.str();
        if (noChains) {
            outals << "    X.chains = stor[X.EV]\n";
        } else {
            outals << "    X.chains = (X.EV -> X.EV)\n";
        }
        outals << "  }\n";
        outals << "  " << line << "\n";
        outals << "}\n";
        outals << "run gentest" << testnum << " for " << numEvents << "\n";
        testnum++;
    }

    return 0;
}
