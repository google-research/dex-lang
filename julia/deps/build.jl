const dexlang_root = dirname(dirname(@__DIR__))
cd(dexlang_root) do 
    run(`make build-ffis`)
end