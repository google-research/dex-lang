// Copyright 2019 Google LLC
//
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file or at
// https://developers.google.com/open-source/licenses/bsd

#include "llvm/ExecutionEngine/Orc/CompileUtils.h"
#include "llvm/ExecutionEngine/Orc/Core.h"
#include "llvm/ExecutionEngine/Orc/ExecutionUtils.h"
#include "llvm/ExecutionEngine/Orc/ExecutorProcessControl.h"
#include "llvm/ExecutionEngine/Orc/IRCompileLayer.h"
#include "llvm/ExecutionEngine/Orc/JITTargetMachineBuilder.h"
#include "llvm/ExecutionEngine/Orc/RTDyldObjectLinkingLayer.h"
#include "llvm/ExecutionEngine/SectionMemoryManager.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Target/TargetMachine.h"
#include <cctype>
#include <cstring>
#include <string>
#include <vector>
#include <cinttypes>
#include <cstdio>
#include <cstddef>
#include <cstdlib>
#include <type_traits>
#include <cstdint>

using namespace llvm;
using namespace llvm::orc;

// Adapted from LLVM's KaleidoscopeJIT demo
class JIT {
public:
  std::unique_ptr<ExecutionSession> ES;
  DataLayout DL;
  MangleAndInterner Mangle;
  RTDyldObjectLinkingLayer ObjectLayer;
  IRCompileLayer CompileLayer;
  JITDylib &MainJD;

  JIT(std::unique_ptr<ExecutionSession> ES,
      JITTargetMachineBuilder JTMB, DataLayout DL)
      : ES(std::move(ES)), DL(std::move(DL)), Mangle(*this->ES, this->DL),
        ObjectLayer(*this->ES,
                    []() { return std::make_unique<SectionMemoryManager>(); }),
        CompileLayer(*this->ES, ObjectLayer,
                     std::make_unique<ConcurrentIRCompiler>(std::move(JTMB))),
        MainJD(this->ES->createBareJITDylib("<main>")) {
    MainJD.addGenerator(
        cantFail(DynamicLibrarySearchGenerator::GetForCurrentProcess(
            DL.getGlobalPrefix())));}

  static Expected<std::unique_ptr<JIT>> Create() {
    InitializeNativeTarget();
    InitializeNativeTargetAsmPrinter();
    InitializeNativeTargetAsmParser();
    auto EPC = SelfExecutorProcessControl::Create();
    if (!EPC) return EPC.takeError();
    auto ES = std::make_unique<ExecutionSession>(std::move(*EPC));
    JITTargetMachineBuilder JTMB(
        ES->getExecutorProcessControl().getTargetTriple());
    auto DL = JTMB.getDefaultDataLayoutForTarget();
    if (!DL) return DL.takeError();
    return std::make_unique<JIT>(std::move(ES), std::move(JTMB), std::move(*DL));
  }

  // Error load_dexrt() {
  // }

  Error add_source(StringRef source) {
    auto context = std::make_unique<LLVMContext>();
    SMDiagnostic Err;
    auto buffer = MemoryBuffer::getMemBuffer(source);
    auto mod = parseIR(buffer->getMemBufferRef(), Err, *context);
    if (!mod) Err.print("Parse error: ", errs());
    mod->setDataLayout(DL);
    verifyModule(*mod, &errs());
    auto RT = MainJD.createResourceTracker();
    auto TSM = ThreadSafeModule(std::move(mod), std::move(context));
    return CompileLayer.add(RT, std::move(TSM));
  }

  Error add_runtime_lib() {
    auto context = std::make_unique<LLVMContext>();
    SMDiagnostic Err;
    auto mod = parseIRFile("src/lib/dexrt.bc", Err, *context);
    if (!mod) Err.print("Parse error: ", errs());
    mod->setDataLayout(DL);
    verifyModule(*mod, &errs());
    auto RT = MainJD.createResourceTracker();
    auto TSM = ThreadSafeModule(std::move(mod), std::move(context));
    return CompileLayer.add(RT, std::move(TSM));
  }

  Expected<JITEvaluatedSymbol> lookup_name(StringRef Name) {
    return ES->lookup({&MainJD}, Mangle(Name.str()));}
};

// === C API ===

static std::unique_ptr<JIT> jit;
ExitOnError ExitOnErr;

extern "C" int initialize_jit() {
  jit = ExitOnErr(JIT::Create());
  ExitOnErr(jit->add_runtime_lib());
  return 0;
}

extern "C" int add_to_jit(char* str_ptr, size_t str_len) {
  ExitOnErr(jit->add_source(StringRef(str_ptr, str_len)));
  return 0;
}

extern "C" void* get_function_ptr(char* str_ptr, size_t str_len) {
  return (void*)((jit->lookup_name(StringRef(str_ptr, str_len)))->getAddress());
}

typedef float (*ftype)();

extern "C" int call_function_ptr(void* f) {
  ((ftype)f)();
  return 0;
}

