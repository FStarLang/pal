<#
.SYNOPSIS
Smoke-test a package built by opt/package.sh with PowerShell only (no bash,
make or MSYS2): unpack it, translate some tests with the packaged pal and
verify them with the bundled F* and Pulse library.

.DESCRIPTION
Meant for Windows without MSYS2, e.g. against the C library headers of MSVC
and the Windows SDK: -Target x86_64-pc-windows-msvc writes a compile_flags.txt
with --target=<triple> next to each test. Clang then finds the headers from
INCLUDE, which must be set, e.g. by vcvars64.bat (MinGW builds of clang, like
pal.exe, cannot locate Visual Studio 2017+ by themselves). Tests run with a
minimal PATH (the package's bin and the system directories), so that no MinGW
gcc on PATH provides C library headers. PAL_SYSROOT is ignored.

Only for tests that are expected to verify (no should-fail or
expected-verification-failures.txt).

.EXAMPLE
pwsh opt/package-test.ps1 dist/pal-0.1.0-abcdef0-windows-x86_64.zip -Target x86_64-pc-windows-msvc
#>
param(
    [Parameter(Mandatory = $true, Position = 0)] [string] $Archive,
    [Parameter(Position = 1, ValueFromRemainingArguments = $true)]
    [string[]] $Tests = @('swap', 'array_alloc', 'bitfields', 'bool_cast', 'break_continue'),
    # Clang target triple, written to each test's compile_flags.txt.
    [string] $Target,
    [switch] $NoVerify
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

function Fail([string] $msg) { Write-Error "FAIL: $msg" -ErrorAction Continue; exit 1 }

$Root = Split-Path -Parent $PSScriptRoot
$Archive = (Resolve-Path $Archive).Path
if ($Target -like '*-msvc' -and -not $env:INCLUDE) {
    Fail 'INCLUDE is not set: run from a Visual Studio developer prompt (vcvars64.bat)'
}
$Tmp = Join-Path ([IO.Path]::GetTempPath()) ("pal-test-" + [Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory $Tmp | Out-Null

try {
    if ($Archive -like '*.zip') {
        Expand-Archive -Path $Archive -DestinationPath $Tmp
    } else {
        tar -xzf $Archive -C $Tmp
        if ($LASTEXITCODE -ne 0) { Fail "cannot unpack $Archive" }
    }
    $Pkg = (Get-ChildItem -Directory (Join-Path $Tmp 'pal-*') | Select-Object -First 1).FullName
    Write-Host "== unpacked to $Pkg"
    Get-Content (Join-Path $Pkg 'BUILDINFO') | Write-Host

    $exe = if ($IsWindows -or $env:OS -eq 'Windows_NT') { '.exe' } else { '' }
    $Pal = Join-Path $Pkg "bin/pal$exe"
    $Fstar = Join-Path $Pkg 'fstar/bin/fstar.exe'

    # A minimal PATH; and no sysroot from the environment.
    if ($exe) {
        $env:PATH = (@((Join-Path $Pkg 'bin'), "$env:SystemRoot\System32", $env:SystemRoot,
                "$env:SystemRoot\System32\Wbem") -join [IO.Path]::PathSeparator)
    } else {
        $env:PATH = (@((Join-Path $Pkg 'bin'), '/usr/bin', '/bin') -join [IO.Path]::PathSeparator)
    }
    Remove-Item Env:PAL_SYSROOT -ErrorAction SilentlyContinue

    & $Pal --help | Out-Null
    if ($LASTEXITCODE -ne 0) { Fail "$Pal does not run" }

    $Verify = -not $NoVerify
    if ($Verify) {
        if (-not (Test-Path $Fstar)) { Fail "no bundled F* in the package ($Fstar)" }
        Write-Host '== bundled F*'
        & $Fstar --version
        if ($LASTEXITCODE -ne 0) { Fail 'the bundled F* does not run' }
        # The shipped Pulse cache must have been checked by this very F*.
        $stamp = Join-Path $Pkg 'pulse/_cache/.fstar-exe.sha256'
        if (-not (Test-Path $stamp)) { Fail 'no checked Pulse library in the package' }
        $expected = ((Get-Content $stamp -Raw).Trim() -split '\s+')[0].ToLowerInvariant()
        $actual = (Get-FileHash -Algorithm SHA256 $Fstar).Hash.ToLowerInvariant()
        if ($expected -ne $actual) { Fail 'the shipped Pulse cache was checked by another F*' }
    }

    $status = 0
    foreach ($t in $Tests) {
        $src = Join-Path $Root "test/$t"
        $dir = Join-Path $Tmp "test/$t"
        New-Item -ItemType Directory $dir -Force | Out-Null
        Get-ChildItem $src -Force | Where-Object { $_.Name -notin 'out', '_cache', 'obj', 'pal.h' } |
            Copy-Item -Destination $dir -Recurse
        # Exercise the packaged annotation header, not the test's copy.
        Copy-Item (Join-Path $Pkg 'include/pal.h') $dir
        if ($Target) {
            Set-Content -Path (Join-Path $dir 'compile_flags.txt') -Value "--target=$Target"
        }
        if ((Test-Path (Join-Path $dir 'should-fail')) -or
            (Test-Path (Join-Path $dir 'expected-verification-failures.txt'))) {
            Fail "$t is expected to fail, which this script does not support"
        }

        Write-Host "== ${t}: $(if ($Verify) { 'verify' } else { 'translate' })"
        Push-Location $dir
        try {
            # As in the test Makefiles.
            $palOpts = @()
            if (Test-Path include) { $palOpts += '-I', 'include' }
            foreach ($f in 'extra_opts', 'pal_opts') {
                if (Test-Path $f) { $palOpts += -split (Get-Content $f -Raw) }
            }
            $cFiles = @(Get-ChildItem -Name -Filter *.c | Sort-Object)
            & $Pal @palOpts --outdir out @cFiles
            $ok = $LASTEXITCODE -eq 0
            if ($ok -and $Verify) {
                $fstarOpts = @('--include', (Join-Path $Pkg 'pulse'),
                    '--include', (Join-Path $Pkg 'pulse/_cache'),
                    '--cache_checked_modules', '--cache_dir', '_cache',
                    '--already_cached', 'Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore',
                    '--include', 'out')
                if (Test-Path helpers) { $fstarOpts += '--include', 'helpers' }
                # F* checks (and caches) the dependencies of each file first.
                $files = @(Get-ChildItem out -Filter *.fsti) + @(Get-ChildItem out -Filter *.fst) |
                    Sort-Object Name | ForEach-Object { "out/$($_.Name)" }
                foreach ($f in $files) {
                    Write-Host "Verifying $f"
                    & $Fstar @fstarOpts $f
                    if ($LASTEXITCODE -ne 0) { $ok = $false; break }
                }
            }
        } finally {
            Pop-Location
        }
        if ($ok) { Write-Host "PASS: $t" } else { Write-Host "FAIL: $t"; $status = 1 }
    }
    exit $status
} finally {
    Remove-Item -Recurse -Force $Tmp -ErrorAction SilentlyContinue
}
