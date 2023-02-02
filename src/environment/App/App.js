import React from 'react';
import {Counter} from 'lib';
import classes from './App.module.scss';

const App = () => (
    <div className={classes.container}>
        <Counter />
    </div>
);

export default App;
