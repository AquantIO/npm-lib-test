import babel from '@rollup/plugin-babel';
import resolve from '@rollup/plugin-node-resolve';
import commonjs from '@rollup/plugin-commonjs';
import postcss from 'rollup-plugin-postcss';
import filesize from 'rollup-plugin-filesize';
import includePaths from 'rollup-plugin-includepaths';
import peerDepsExternal from 'rollup-plugin-peer-deps-external';
import autoprefixer from 'autoprefixer';
import stylelint from 'rollup-plugin-stylelint';
import postcssPresetEnv from 'postcss-preset-env';
import {terser} from 'rollup-plugin-terser';
import pkg from './package.json';

const importPathToInput = {
    '.': 'src/lib/index.js',
    './icons': 'src/lib/icons.js',
};

(() => {
    const existingInExports = new Set(Object.keys(pkg.exports));
    Object.keys(importPathToInput).forEach(importPath => {
        if (!existingInExports.has(importPath)) {
            throw new Error(`rollup config error! missing item ${importPath} in package.json exports`);
        }
        existingInExports.delete(importPath);
    });

    if (existingInExports.size > 0) {
        throw new Error(`rollup config error! missing items ${[...existingInExports]} in importPathToInput`);
    }
})();

const outputs = Object.entries(pkg.exports).map(([importPath, exportFile]) => ({
    input: importPathToInput[importPath],
    file: exportFile,
}));

const postcssPlugins = [
    postcssPresetEnv({
        browsers: pkg.browserslist.production,
        stage: 3,
    }),
    autoprefixer(),
];

const config = outputs.map(({file, input}) => ({
    input,
    output: {
        file,
        format: 'esm',
        exports: 'named',
    },
    plugins: [
        peerDepsExternal(),
        includePaths({
            include: {},
            paths: ['src'],
            external: Object.keys(pkg.dependencies),
            extensions: ['.jsx', '.js', '.json', '.html'],
        }),
        stylelint({
            throwOnError: true,
        }),
        postcss({
            extract: process.env.REACT_APP_PKG_STYLE || pkg.style,
            inline: false,
            plugins: postcssPlugins,
            modules: {
                generateScopedName: 'Aqui-[name]__[local]___[hash:base64:5]',
            },
        }),
        babel({
            babelHelpers: 'bundled',
            exclude: 'node_modules/**',
            configFile: './babel.config.rollup.js',
        }),
        resolve({
            browser: true,
        }),
        commonjs(),
        terser(),
        filesize(),
    ],
}));

export default config;
