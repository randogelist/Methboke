@echo off
setlocal EnableExtensions DisableDelayedExpansion
set "PKG=FEF_NSE_MASTERAC_TWO_LAYER_LEAN_v0_11_0"
set "ROOT=%~dp0"
set "LEAN_NUM_THREADS=16"
set "STAGE=START"
set "PUSHED=NO"
echo RUNNER_ENTERED=PASS
echo PACKAGE=%PKG%
echo MODE=CORE_ONLY_INTERNAL_KERNEL_RECONSTRUCTION
echo NETWORK=NOT_USED
echo PYTHON=NOT_USED
echo POWERSHELL=NOT_USED
echo LAKE=NOT_USED
echo DEPENDENCY_DOWNLOAD=DISABLED
echo LEAN_NUM_THREADS=16
echo PUBLIC_LAYOUT=LayerA_Mathematics,LayerB_Physics,MasterAC,PhysicsUnification,Master_r3,Master_T3,Feffermann-Classification

if not defined LEAN_EXE set "LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe"
set "STAGE=LOCATE_COMPILER"
if not exist "%LEAN_EXE%" goto failed
echo LEAN_EXE=%LEAN_EXE%
set "STAGE=CREATE_OUTPUT"
if not exist "%ROOT%build" mkdir "%ROOT%build"
if not exist "%ROOT%build" goto failed

:choose_output
set "BUILD=%ROOT%build\run_%RANDOM%_%RANDOM%"
if exist "%BUILD%" goto choose_output
mkdir "%BUILD%"
if errorlevel 1 goto failed
mkdir "%BUILD%\Fefferman"
if errorlevel 1 goto failed
mkdir "%BUILD%\logs"
if errorlevel 1 goto failed
echo BUILD_DIRECTORY=%BUILD%

set "STAGE=VERSION_CHECK"
"%LEAN_EXE%" --version > "%BUILD%\logs\version.log" 2>&1
if errorlevel 1 goto failed
type "%BUILD%\logs\version.log"
findstr /L /C:"version 4.33.0," "%BUILD%\logs\version.log" >nul
if errorlevel 1 goto failed
echo LEAN_VERSION_CHECK=PASS

set "STAGE=COPY_SOURCES"
if not exist "%ROOT%modules.txt" goto failed
copy /y "%ROOT%Fefferman\*.lean" "%BUILD%\Fefferman\" >nul
if errorlevel 1 goto failed
copy /y "%ROOT%*.lean" "%BUILD%\" >nul
if errorlevel 1 goto failed
copy /y "%ROOT%modules.txt" "%BUILD%\modules.txt" >nul
if errorlevel 1 goto failed
copy /y "%ROOT%modules_layer_a.txt" "%BUILD%\modules_layer_a.txt" >nul
if errorlevel 1 goto failed
copy /y "%ROOT%modules_layer_b.txt" "%BUILD%\modules_layer_b.txt" >nul
if errorlevel 1 goto failed

pushd "%BUILD%"
if errorlevel 1 goto failed
set "PUSHED=YES"
set "LEAN_PATH=%BUILD%"
set "STAGE=SOURCE_SCAN"
for /f "usebackq delims=" %%M in ("modules.txt") do (
  call :scan "%%M"
  if errorlevel 1 goto failed
)
echo PROJECT_PROOF_ESCAPE_SCAN=PASS
echo PROJECT_RESEARCH_AXIOM_DECLARATIONS=0

set "STAGE=LAYER_A_MATHEMATICS"
for /f "usebackq delims=" %%M in ("modules_layer_a.txt") do (
  call :compile "%%M"
  if errorlevel 1 goto failed
)
echo LAYER_A_MATHEMATICS=PASS

set "STAGE=LAYER_B_PHYSICS"
for /f "usebackq delims=" %%M in ("modules_layer_b.txt") do (
  call :compile "%%M"
  if errorlevel 1 goto failed
)
echo LAYER_B_PHYSICS=PASS

set "STAGE=AUDIT"
call :compile "Audit"
if errorlevel 1 goto failed

set "STAGE=PRINTED_AXIOM_AUDIT"
findstr /L /C:"sorryAx" /C:"Lean.ofReduceBool" /C:"Lean.trustCompiler" "logs\Audit.log" >nul
if not errorlevel 1 goto failed
if errorlevel 2 goto failed
for /f %%N in ('find /c "axioms" ^< "logs\Audit.log"') do set "AUDIT_LINES=%%N"
if not "%AUDIT_LINES%"=="362" goto failed
copy /y "logs\Audit.log" "logs\axioms.log" >nul
if errorlevel 1 goto failed
echo PRINTED_THEOREM_AXIOM_REPORTS=%AUDIT_LINES%
echo NO_SORRYAX_IN_PRINTED_REPORT=PASS
echo PROJECT_BUILD=PASS
echo ANALYTIC_REALIZATION=OPEN
echo ROCQ_TO_LEAN_PORTS=PARTIAL
echo ANALYTIC_ENDPOINTS=OPEN
echo MASTER_IMPLICATIONS=KERNEL_ELABORATED_CONDITIONAL
echo LEGACY_POSITIVE_A_C_TARGET_INSTANCE=OPEN
echo LEGACY_POSITIVE_B_D_TARGET_INSTANCE=OPEN
echo BREAKDOWN_REGIME_NONEMPTINESS=OPEN
echo SOURCE_MASTER_MR3=KERNEL_ELABORATED_CONDITIONAL_THEOREM_COLLECTION
echo SOURCE_MASTER_MT3=KERNEL_ELABORATED_CONDITIONAL_THEOREM_COLLECTION
echo NEW_BRANCH_ALGEBRA=KERNEL_ELABORATED_CONDITIONAL
echo FINITE_SPECTRAL_EMBEDDINGS=KERNEL_ELABORATED_CONDITIONAL
echo REDUCED_CAPACITY_TRANSPORT=KERNEL_ELABORATED_CONDITIONAL
echo SPECTRAL_SAME_VECTOR_BINDING=EXPLICIT
echo QUATROS_INTERNAL_PORT=CONSTRUCTED_FOR_EXPLICIT_OBSERVABLES
echo MAOTAOTROS_INTERNAL_PORT=CONSTRUCTED_FROM_DIFFERENTIAL_AND_CANONICAL_DATA
echo COVARIANCE_PREFIX_PORT=CONSTRUCTED_FOR_EACH_DOMAIN
echo CAUSAL_PATH_AND_509_RENEWAL=KERNEL_ELABORATED_CONDITIONAL
echo SUPPLIED_STORAGE_AND_PAID_PREFIX=KERNEL_ELABORATED_CONDITIONAL
echo CANONICAL_SIGNED_BUDGET=KERNEL_ELABORATED_CONDITIONAL
echo MODAL_PACKET_CONSTRUCTION_PORTS=PARTIAL
echo ROCQ_PROOFS_PENDING_LEAN_PORTS=SEPARATELY_INDEXED
echo CROSS_BRANCH_SAME_OBJECT_BINDINGS=PARTIAL
echo R3_OCCUPATION_TO_ACTION_PORT=OPEN
echo T3_FOURIER_AND_RENEWAL_REALIZATION=OPEN
echo FEFFERMAN_R3_INTRINSIC_IDENTIFICATION=KERNEL_BRIDGE_ADDED
echo MOVING_PARSEVAL_FRAME_FINITE_CUTOFF=KERNEL_TARGET
echo MOVING_HILBERT_BASIS_CONTINUUM=OPEN_ANALYTIC_LIMIT
echo PHYSICS_VARIATIONAL_TRANSPORT=KERNEL_TARGET
echo PHYSICS_CM_EULER_LAGRANGE_DERIVATION=KERNEL_TARGET
echo PHYSICS_QM_GP_SHIFT_CCR_DERIVATION=KERNEL_TARGET
echo PHYSICS_QM_PICTURE_DUALITY=KERNEL_TARGET
echo PHYSICS_GR_CARTAN_ACTION_EXPANSION=KERNEL_TARGET
echo PHYSICS_GR_METRIC_RECONSTRUCTION=KERNEL_TARGET
echo PHYSICS_GR_EINSTEIN_DYNAMICS=EXPLICIT_REALIZATION_PORT
echo PHYSICS_QM_GR_ROUNDTRIP_EQUIVALENCE=OPEN
echo LAYER_A_PUBLIC_ENTRY=LayerA_Mathematics
echo LAYER_A_DEPENDS_ON_PHYSICS=NO
echo LAYER_B_PUBLIC_ENTRY=LayerB_Physics
echo LAYER_B_DEPENDS_ON_LAYER_A=YES
echo MASTER_AC_LAYER=LEAN_ENCODED_NONCIRCULAR
echo MASTER_AC_TO_FEFFERMAN_AC=KERNEL_ELABORATED_CONDITIONAL
echo MASTER_AC_INTERNAL_BREAKDOWN_FAMILY=OPEN
echo MASTER_AC_PHYSICAL_PROJECTION_REALIZATION=OPEN
echo FEFFERMAN_R3_FORCE_EMBEDDING=STANDARD_ANALYSIS_ESTIMATE_DOCUMENTED
echo R3_INTRINSIC_GLOBAL_CLOSURE=OPEN_PDE_FRONTIER
echo NSE_CASE_PROVED=NONE
echo STATUS=FEFFERMAN_INTERNAL_KERNEL_RECONSTRUCTION_CONDITIONAL
echo LOGS=%BUILD%\logs
>"SUCCESS.txt" echo RUN=PASS
>>"SUCCESS.txt" echo SCOPE=INTERNAL_KERNEL_RECONSTRUCTION_CONDITIONAL
>>"SUCCESS.txt" echo ANALYTIC_REALIZATION_AND_ROUTE_PORTS=OPEN
echo RUN=PASS
popd
endlocal
exit /b 0

:scan
if not exist "%~1.lean" exit /b 1
findstr /N /R /C:"\<sorry\>" /C:"\<admit\>" /C:"\<axiom\>" /C:"\<opaque\>" /C:"\<unsafe\>" /C:"\<native_decide\>" /C:"implemented_by" /C:"extern" "%~1.lean"
if not errorlevel 1 exit /b 1
if errorlevel 2 exit /b 1
exit /b 0

:compile
echo COMPILE_START=%~1
"%LEAN_EXE%" -j 16 -o "%~1.olean" "%~1.lean" > "logs\%~nx1.log" 2>&1
if errorlevel 1 (
  type "logs\%~nx1.log"
  exit /b 1
)
if not exist "%~1.olean" exit /b 1
for %%F in ("%~1.olean") do if %%~zF LEQ 0 exit /b 1
echo COMPILE_PASS=%~1
exit /b 0

:failed
echo FAIL_STAGE=%STAGE%
if defined BUILD echo LOGS=%BUILD%\logs
echo RUN=FAIL
if "%PUSHED%"=="YES" popd
endlocal
exit /b 1
